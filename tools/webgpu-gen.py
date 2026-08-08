#!/usr/bin/env python3
"""WebGPU binding generator: webgpu.idl -> stdlib/webgpu.fpp + glue tables.

The model the emitters consume is deliberately dumb JSON: enums (string
mapped), dictionaries (records with optional fields), interfaces (int-handle
classes), typedefs, namespaces, includes. Run with 'model' to dump it.
"""
import re, sys, json

def strip_comments(s):
    s = re.sub(r'//[^\n]*', '', s)
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.S)
    return s

def parse(idl):
    idl = strip_comments(idl)
    # drop extended attributes that precede declarations
    idl = re.sub(r'\[[^\]]+\]\s*', '', idl)
    out = {'enums': {}, 'dicts': {}, 'interfaces': {}, 'typedefs': {},
           'namespaces': {}, 'includes': [], 'flags': {}}
    # enum X { "a", "b" };
    for m in re.finditer(r'enum\s+(\w+)\s*\{([^}]*)\}\s*;', idl):
        vals = re.findall(r'"([^"]*)"', m.group(2))
        out['enums'][m.group(1)] = vals
    # typedefs (incl. flag typedefs like GPUBufferUsageFlags)
    for m in re.finditer(r'typedef\s+(.+?)\s+(\w+)\s*;', idl):
        out['typedefs'][m.group(2)] = m.group(1).strip()
    # dictionary X [: Base] { members }; — BRACE-BALANCED (defaults like
    # `= {}` live inside bodies)
    def balanced(src, start):
        depth, i = 0, start
        while i < len(src):
            if src[i] == '{': depth += 1
            elif src[i] == '}':
                depth -= 1
                if depth == 0: return src[start + 1:i], i
            i += 1
        return src[start + 1:], len(src)
    for m in re.finditer(r'dictionary\s+(\w+)(?:\s*:\s*(\w+))?\s*\{', idl):
        name, base = m.group(1), m.group(2)
        body, _ = balanced(idl, m.end() - 1)
        members = []
        for stmt in body.split(';'):
            stmt = stmt.strip()
            if not stmt: continue
            mm = re.match(r'^(required\s+)?(.+?)\s+(\w+)(?:\s*=\s*(.+))?$', stmt, flags=re.S)
            if mm:
                req, ty, mname, dflt = mm.group(1), mm.group(2).strip(), mm.group(3), mm.group(4)
                members.append({'name': mname, 'type': ty, 'required': bool(req),
                                'default': dflt.strip() if dflt else None})
        out['dicts'][name] = {'base': base, 'members': members}
    # interface / namespace bodies — BRACE-BALANCED like dictionaries
    # (method defaults such as `= {}` live inside)
    for kind, rx in [('interfaces', r'interface\s+(?:mixin\s+)?(\w+)(?:\s*:\s*(\w+))?\s*\{'),
                     ('namespaces', r'namespace\s+(\w+)\s*\{')]:
        for m in re.finditer(rx, idl):
            if kind == 'interfaces':
                name, base = m.group(1), m.group(2)
            else:
                name, base = m.group(1), None
            body, _ = balanced(idl, m.end() - 1)
            # PARTIAL declarations merge into the first
            prev = out[kind].get(name)
            attrs = prev['attrs'] if prev else []
            methods = prev['methods'] if prev else []
            consts = prev['consts'] if prev else []
            if prev and prev.get('base') and not base:
                base = prev['base']
            for line in body.split(';'):
                line = line.strip()
                if not line: continue
                cm = re.match(r'const\s+([\w\s]+?)\s+(\w+)\s*=\s*(.+)$', line)
                if cm:
                    consts.append({'name': cm.group(2), 'value': cm.group(3).strip()})
                    continue
                am = re.match(r'(?:readonly\s+)?attribute\s+(.+?)\s+(\w+)$', line)
                if am:
                    attrs.append({'name': am.group(2), 'type': am.group(1).strip(),
                                  'readonly': line.startswith('readonly')})
                    continue
                fm = re.match(r'([\w<>\?\s]+?)\s+(\w+)\s*\((.*)\)$', line, flags=re.S)
                if fm:
                    ret, mname, args = fm.group(1).strip(), fm.group(2), fm.group(3)
                    arglist = []
                    if args.strip():
                        for a in split_args(args):
                            aa = re.match(r'(optional\s+)?(.+?)\s+(\w+)(?:\s*=\s*(.+))?$', a.strip(), flags=re.S)
                            if aa:
                                arglist.append({'name': aa.group(3), 'type': aa.group(2).strip(),
                                                'optional': bool(aa.group(1)),
                                                'default': aa.group(4).strip() if aa.group(4) else None})
                    methods.append({'name': mname, 'ret': ret, 'args': arglist})
            out[kind][name] = {'base': base, 'attrs': attrs, 'methods': methods, 'consts': consts}
    for m in re.finditer(r'(\w+)\s+includes\s+(\w+)\s*;', idl):
        out['includes'].append([m.group(1), m.group(2)])
    return out

def split_args(s):
    # comma split respecting <> and () nesting
    parts, depth, cur = [], 0, ''
    for ch in s:
        if ch in '<(': depth += 1
        elif ch in '>)': depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur); cur = ''
        else: cur += ch
    if cur.strip(): parts.append(cur)
    return parts

if __name__ == '__main__':
    model = parse(open('tools/webgpu.idl').read())
    if 'model' in sys.argv:
        print(json.dumps(model, indent=1))
    else:
        print('enums', len(model['enums']), '| dicts', len(model['dicts']),
              '| interfaces', len(model['interfaces']), '| typedefs', len(model['typedefs']),
              '| namespaces', len(model['namespaces']), '| includes', len(model['includes']))
        # sanity: the hello-triangle surface must be present
        for need in ['GPUTextureFormat', 'GPULoadOp']:
            assert need in model['enums'], need
        for need in ['GPURenderPipelineDescriptor', 'GPURenderPassColorAttachment']:
            assert need in model['dicts'], need
        for need in ['GPUDevice', 'GPUCommandEncoder', 'GPURenderPassEncoder', 'GPUCanvasContext']:
            assert need in model['interfaces'], need
        print('hello-triangle surface: present')

# ---- emitter ---------------------------------------------------------------

def pascal(name):
    parts = re.split(r'[-_ ]', name)
    out = ''.join(p[:1].upper() + p[1:] for p in parts if p)
    if out and out[0].isdigit():
        # "1d" -> "D1", "2d-array" -> "D2Array"
        m = re.match(r'(\d+)(\w)(.*)', out)
        out = m.group(2).upper() + m.group(1) + m.group(3)
    return out

def resolve(model, ty):
    seen = set()
    while ty in model['typedefs'] and ty not in seen:
        seen.add(ty)
        ty = model['typedefs'][ty]
    return ty

def fpp_type(model, ty):
    """IDL type -> (fpp type, kind) — kind drives marshaling."""
    ty = ty.strip()
    if ty.endswith('?'): ty = ty[:-1].strip()
    ty = resolve(model, ty)
    m = re.match(r'Promise<(.+)>$', ty)
    if m:
        inner, k = fpp_type(model, m.group(1).strip())
        return ('Future<%s>' % inner, ('future', k))
    m = re.match(r'sequence<(.+)>$', ty)
    if m:
        inner, k = fpp_type(model, m.group(1).strip())
        return ('%s[]' % inner, ('seq', k, inner))
    if ty.startswith('(') or ' or ' in ty:
        # union: a dictionary alternative wins (record + optional fields);
        # else the LAST interface alternative (samples pass views, and
        # `(GPUTexture or GPUTextureView)` lists the view last); else raw
        parts = [resolve(model, p.strip().rstrip('?')) for p in re.split(r'\s+or\s+', ty.strip('() '))]
        for part in parts:
            if part in model['enums']:
                return fpp_type(model, part)   # `layout: "auto"` and kin
        for part in parts:
            if part in model['dicts']:
                return fpp_type(model, part)
        for part in reversed(parts):
            if part in model['interfaces']:
                return fpp_type(model, part)
        return ('JsObj', ('raw',))
    prim = {'boolean': ('bool', ('bool',)), 'undefined': ('unit', ('unit',)),
            'DOMString': ('string', ('string',)), 'USVString': ('string', ('string',)),
            'float': ('float', ('num',)), 'double': ('float', ('num',)),
            'unrestricted float': ('float', ('num',)), 'unrestricted double': ('float', ('num',)),
            'long long': ('float', ('num',)), 'unsigned long long': ('float', ('num',)),
            'unsigned long': ('int', ('int',)), 'long': ('int', ('int',)),
            'unsigned short': ('int', ('int',)), 'short': ('int', ('int',)),
            'octet': ('int', ('int',)), 'any': ('JsObj', ('raw',)), 'object': ('JsObj', ('raw',))}
    if ty in prim: return prim[ty]
    if ty in model['enums']: return (ty, ('enum', ty))
    if ty in model['dicts']: return (ty, ('dict', ty))
    if ty in model['interfaces']:
        # only GPU-prefixed non-mixin interfaces are emitted as classes;
        # anything else crosses raw
        if ty.startswith('GPU') and ty not in model.get('mixins', set()):
            return (ty, ('iface', ty))
        return ('JsObj', ('raw',))
    return ('JsObj', ('raw',))

def to_js(model, kind, expr):
    k = kind[0]
    if k == 'bool': return 'Js.ofBool (%s)' % expr
    if k == 'string': return 'Js.ofString (%s)' % expr
    if k == 'num': return 'Js.ofNum (%s)' % expr
    if k == 'int': return 'Js.ofNum (float (%s))' % expr
    if k == 'enum': return 'Marshal.%sJs (%s)' % (kind[1], expr)
    if k == 'dict': return 'Marshal.%sJs (%s)' % (kind[1], expr)
    if k == 'iface': return 'Js.handle (%s).H' % expr
    if k == 'seq': return 'Marshal.SeqJs (fun x -> %s) (%s)' % (to_js(model, kind[1], 'x'), expr)
    return expr

def of_js(model, kind, expr):
    k = kind[0]
    if k == 'bool': return 'Js.toBool (%s)' % expr
    if k == 'string': return 'Js.toString (%s)' % expr
    if k == 'num': return 'Js.toNum (%s)' % expr
    if k == 'int': return 'int (Js.toNum (%s))' % expr
    if k == 'enum': return 'Marshal.%sOfJs (Js.toString (%s))' % (kind[1], expr)
    if k == 'iface': return None  # handled by caller (register + watch)
    if k == 'unit': return None
    return expr

def emit(model):
    # `A includes B`: mixin members join the including interface; the
    # mixins themselves are not emitted
    mixin_names = set()
    for target, mixin in model['includes']:
        if mixin in model['interfaces'] and target in model['interfaces']:
            mixin_names.add(mixin)
            for lst in ('attrs', 'methods', 'consts'):
                model['interfaces'][target][lst] = \
                    model['interfaces'][target][lst] + model['interfaces'][mixin][lst]
    model['mixins'] = mixin_names
    L = []
    a = L.append
    a('// GENERATED by tools/webgpu-gen.py from tools/webgpu.idl — do not edit.')
    a('// The complete WebGPU surface: real enums, record descriptors with')
    a('// optional fields, INT-HANDLE object wrappers (a strong JS-side table,')
    a('// freed by a FinalizationRegistry watching these wasm wrappers), and')
    a('// Future<...> for every Promise. Browser-only: guard uses with #if WASM.')
    a('module WebGpu')
    a('')
    # enums
    for en, vals in model['enums'].items():
        a('type %s =' % en)
        for i, v in enumerate(vals):
            a('    | %s = %d' % (pascal(v), i))
        a('')
    # flag namespaces (GPUBufferUsage etc): constants as ints
    for nn, ns in model['namespaces'].items():
        if not ns['consts']: continue
        a('module %s =' % nn)
        for c in ns['consts']:
            a('    let %s : int = %s' % (pascal(c['name'].lower()), int(c['value'], 0)))
        a('')
    # the chain: interfaces, dicts, Marshal
    first = True
    def hdr(name, suffix):
        nonlocal first
        kw = 'type' if first else 'and'
        first = False
        return '%s %s%s' % (kw, name, suffix)
    for iname, iface in model['interfaces'].items():
        if not iname.startswith('GPU') or iname in model['mixins']: continue
        a(hdr(iname, '(h : int) ='))
        a('    member x.H : int = h')
        for at in iface['attrs']:
            t, k = fpp_type(model, at['type'])
            if k[0] in ('dict', 'seq'): t, k = 'JsObj', ('raw',)
            get = 'Js.get (Js.handle h) "%s"' % at['name']
            if k[0] == 'future':
                a('    member x.%s : %s =' % (pascal(at['name']), t))
                body_wrap(a, model, k, get, t)
            elif k[0] == 'iface':
                a('    member x.%s : %s =' % (pascal(at['name']), t))
                a('        let r = Js.register (%s)' % get)
                a('        let w = %s r' % t)
                a('        Js.watch (box w) r')
                a('        w')
            else:
                conv = of_js(model, k, get)
                if conv: a('    member x.%s : %s = %s' % (pascal(at['name']), t, conv))
        for me in iface['methods']:
            rt, rk = fpp_type(model, me['ret'])
            # dict/seq RETURNS have no reverse marshal (v1): raw JsObj
            if rk[0] in ('dict', 'seq'): rt, rk = 'JsObj', ('raw',)
            if rk[0] == 'future' and rk[1][0] in ('dict', 'seq'):
                rt, rk = 'Future<JsObj>', ('future', ('raw',))
            args = []
            for ar in me['args']:
                at_, ak = fpp_type(model, ar['type'])
                args.append((ar['name'], at_, ak, ar['optional']))
            all_opt = bool(args) and all(opt for _, _, _, opt in args)
            mname = pascal(me['name'])
            if all_opt:
                # JS samples call these bare: the bare form keeps the name;
                # the with-arguments form is NAMED (`CreateViewWith`) —
                # same-name overloads trip a selector bug, see
                # tests/known-issues/member-overload-crosstalk
                a('    member x.%s () : %s =' % (mname, rt))
                call0 = 'Js.call0 (Js.handle h) "%s"' % me['name']
                body_wrap(a, model, rk, call0, rt)
                args = [(n, t, k2, False) for n, t, k2, _ in args]
                mname = mname + 'With'
            sig = ', '.join('%s%s : %s' % ('?' if opt else '', n, t) for n, t, _, opt in args)
            a('    member x.%s (%s) : %s =' % (mname, sig, rt))
            # marshal each arg to a JsObj local
            for n, t, ak, opt in args:
                if opt:
                    a('        let %s_j = (match %s with Some v -> %s | None -> Js.undefined ())'
                      % (n, n, to_js(model, ak, 'v')))
                else:
                    a('        let %s_j = %s' % (n, to_js(model, ak, n)))
            call = 'Js.call%d (Js.handle h) "%s"%s' % (
                len(args), me['name'], ''.join(' %s_j' % n for n, _, _, _ in args))
            body_wrap(a, model, rk, call, rt)
        a('')
    for dname, d in model['dicts'].items():
        # flatten inheritance: base members join the record
        members, seen, cur = [], set(), dname
        chain = []
        while cur and cur in model['dicts']:
            chain.append(cur)
            cur = model['dicts'][cur]['base']
        for cn in reversed(chain):
            for mm in model['dicts'][cn]['members']:
                if mm['name'] not in seen:
                    seen.add(mm['name']); members.append(mm)
        a(hdr(dname, ' = {'))
        for mm in members:
            t, k = fpp_type(model, mm['type'])
            q = '' if mm['required'] else '?'
            a('    %s%s : %s' % (q, pascal(mm['name']), t))
        a('    }')
        a('')
    # Marshal statics close the chain
    a('and Marshal =')
    a('    static member SeqJs (f : \'a -> JsObj) (xs : \'a[]) : JsObj =')
    a('        let a = Js.newArr ()')
    a('        let mutable i = 0')
    a('        while i < xs.Length do')
    a('            Js.push a (f xs.[i])')
    a('            i <- i + 1')
    a('        a')
    for en, vals in model['enums'].items():
        a('    static member %sJs (v : %s) : JsObj =' % (en, en))
        a('        Js.ofString (match v with')
        for v in vals:
            a('                     | %s.%s -> "%s"' % (en, pascal(v), v))
        a('                     | _ -> "%s")' % vals[0])
        a('    static member %sOfJs (s : string) : %s =' % (en, en))
        a('        (match s with')
        for v in vals:
            a('         | "%s" -> %s.%s' % (v, en, pascal(v)))
        a('         | _ -> %s.%s)' % (en, pascal(vals[0])))
    for dname, d in model['dicts'].items():
        members, seen, cur, chain = [], set(), dname, []
        while cur and cur in model['dicts']:
            chain.append(cur)
            cur = model['dicts'][cur]['base']
        for cn in reversed(chain):
            for mm in model['dicts'][cn]['members']:
                if mm['name'] not in seen:
                    seen.add(mm['name']); members.append(mm)
        a('    static member %sJs (r : %s) : JsObj =' % (dname, dname))
        a('        let o = Js.newObj ()')
        for mm in members:
            t, k = fpp_type(model, mm['type'])
            f = pascal(mm['name'])
            if mm['required']:
                a('        Js.set o "%s" (%s)' % (mm['name'], to_js(model, k, 'r.%s' % f)))
            else:
                a('        (match r.%s with' % f)
                a('         | Some v -> Js.set o "%s" (%s)' % (mm['name'], to_js(model, k, 'v')))
                a('         | None -> ())')
        a('        o')
    a('')
    # cross-file class CONSTRUCTORS do not lower (known compiler gap);
    # these same-file helpers are the wrap points other files call
    for iname in model['interfaces']:
        if iname.startswith('GPU') and iname not in model['mixins']:
            a('let Wrap%s (h : int) : %s = %s h' % (iname, iname, iname))
    a('')
    a('/// navigator.gpu — the entry point')
    a('let Gpu () : GPU =')
    a('    let r = Js.register (Js.get (Js.global_ "navigator") "gpu")')
    a('    let w = GPU r')
    a('    Js.watch (box w) r')
    a('    w')
    return '\n'.join(L) + '\n'

def body_wrap(a, model, rk, call, rt):
    k = rk[0]
    if k == 'future':
        inner_k = rk[1]
        a('        future {')
        a('            let! p = Js.futureOf (%s)' % call)
        ik = inner_k[0]
        if ik == 'iface':
            a('            let r = Js.register p')
            a('            let w = %s r' % inner_k[1])
            a('            Js.watch (box w) r')
            a('            return w')
        elif ik == 'unit':
            a('            return (let _u = p in ())')
        else:
            conv = of_js(model, inner_k, 'p')
            a('            return %s' % (conv if conv else 'p'))
        a('        }')
    elif k == 'iface':
        a('        let r = Js.register (%s)' % call)
        a('        let w = %s r' % rk[1])
        a('        Js.watch (box w) r')
        a('        w')
    elif k == 'unit':
        a('        %s |> ignore' % call)
    else:
        conv = of_js(model, rk, call)
        a('        %s' % (conv if conv else call))

if 'emit' in sys.argv:
    model = parse(open('tools/webgpu.idl').read())
    open('stdlib/webgpu.fpp', 'w').write(emit(model))
    print('stdlib/webgpu.fpp written')
