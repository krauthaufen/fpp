#!/usr/bin/env python3
"""WebGL binding generator: Khronos webgl.idl + webgl2.idl -> stdlib/webgl.fpp.

Reuses webgpu-gen.py's WebIDL parser. GL constants become ONE real GLenum
(true numeric values, PascalCase); handles are int-handle classes over the
same JS-side registry; same-name overloads keep the first form and emit the
rest with an arity suffix.
"""
import re, sys
_full = open('tools/webgpu-gen.py').read()
exec(_full.split('# ---- emitter')[0])                     # parser
_tail = _full.split('# ---- emitter')[1]
_helpers = _tail[_tail.index('def pascal'):_tail.index('def to_js')]
exec(_helpers)                                             # pascal/resolve/fpp_type

def parse_all():
    idl = open('tools/webgl1.idl').read() + '\n' + open('tools/webgl2.idl').read()
    model = parse(idl)
    # the EXTENSION registry (tools/webgl-ext.idl, vendored from Khronos):
    # each `// EXT <name>` header names one extension object reachable via
    # getExtension(name); other interfaces in the file are handle classes
    ext_src = open('tools/webgl-ext.idl').read()
    ext_names = re.findall(r'^// EXT (\S+)', ext_src, re.M)
    ext_model = parse(ext_src)
    model['typedefs'].update(ext_model['typedefs'])
    for n, i in ext_model['interfaces'].items():
        if n not in model['interfaces']:
            model['interfaces'][n] = i
    model['extensions'] = [n for n in ext_names if n in ext_model['interfaces']]
    return model

GLPRIM = {
    'GLenum': ('GLenum', 'enum'), 'GLboolean': ('bool', 'bool'),
    'GLbitfield': ('int', 'int'), 'GLbyte': ('int', 'int'), 'GLshort': ('int', 'int'),
    'GLint': ('int', 'int'), 'GLsizei': ('int', 'int'), 'GLintptr': ('float', 'num'),
    'GLsizeiptr': ('float', 'num'), 'GLubyte': ('int', 'int'), 'GLushort': ('int', 'int'),
    'GLuint': ('int', 'int'), 'GLfloat': ('float', 'num'), 'GLclampf': ('float', 'num'),
    'GLint64': ('float', 'num'), 'GLuint64': ('float', 'num'),
    'boolean': ('bool', 'bool'), 'undefined': ('unit', 'unit'),
    'DOMString': ('string', 'string'), 'USVString': ('string', 'string'),
    'float': ('float', 'num'), 'double': ('float', 'num'),
    'long': ('int', 'int'), 'unsigned long': ('int', 'int'),
    'any': ('JsObj', 'raw'), 'object': ('JsObj', 'raw'),
}

def gl_type(model, handles, ty):
    ty = ty.strip()
    if ty.endswith('?'): ty = ty[:-1].strip()
    if ty in GLPRIM: return GLPRIM[ty]     # BEFORE typedef resolution:
    ty = resolve(model, ty)                # GLenum is typedef'd to a plain
    if ty.endswith('?'): ty = ty[:-1].strip()  # integer in the IDL
    if ty in GLPRIM: return GLPRIM[ty]
    if ty in handles: return (ty, 'iface')
    m = re.match(r'sequence<(.+)>$', ty)
    if m:
        # a sequence of scalars/enums crosses as a typed ARRAY, marshaled
        # into a JS array element by element; anything richer stays raw
        it, ik = gl_type(model, handles, m.group(1))
        if ik in ('enum', 'int', 'num', 'bool', 'string'):
            return ('%s[]' % it, 'seq:' + ik)
        return ('JsObj', 'raw')
    return ('JsObj', 'raw')

def arg_in(t, k, expr):
    if k == 'enum': return 'Js.ofNum (float (int (%s)))' % expr
    if k == 'bool': return 'Js.ofBool (%s)' % expr
    if k == 'int': return 'Js.ofNum (float (%s))' % expr
    if k == 'num': return 'Js.ofNum (%s)' % expr
    if k == 'string': return 'Js.ofString (%s)' % expr
    if k == 'iface': return 'Js.handle (%s).H' % expr
    return expr

def ret_out(a, t, k, call, wrapname):
    if k == 'unit': a('        %s |> ignore' % call)
    elif k == 'iface':
        a('        let r = Js.register (%s)' % call)
        a('        let w = %s r' % t)
        a('        Js.watch (box w) r')
        a('        w')
    elif k == 'enum': a('        (Marshal.GLenumOf (int (Js.toNum (%s))))' % call)
    elif k == 'bool': a('        Js.toBool (%s)' % call)
    elif k == 'int': a('        int (Js.toNum (%s))' % call)
    elif k == 'num': a('        Js.toNum (%s)' % call)
    elif k == 'string': a('        Js.toString (%s)' % call)
    else: a('        %s' % call)

def emit_method(a, model, handles, mname, me):
    args = []
    for ar in me['args']:
        t, k = gl_type(model, handles, ar['type'])
        an = ar['name']
        if an in ('type', 'end', 'begin', 'to', 'done', 'val', 'ref'):
            an = an + "'"
        args.append((an, t, k))
    rt, rk = gl_type(model, handles, me['ret'])
    if rk.startswith('seq:'):
        # typed sequences are an ARGUMENT convenience; a returned one has
        # no reverse marshal and crosses raw
        rt, rk = 'JsObj', 'raw'
    sig = ', '.join('%s : %s' % (n, t) for n, t, _ in args)
    a('    member x.%s (%s) : %s =' % (mname, sig, rt))
    for n, t, k in args:
        if k.startswith('seq:'):
            a('        let %s_j = Js.newArr ()' % n)
            a('        for si in 0 .. Array.length %s - 1 do Js.push %s_j (%s)'
              % (n, n, arg_in('', k[4:], '%s.[si]' % n)))
        else:
            a('        let %s_j = %s' % (n, arg_in(t, k, n)))
    call = 'Js.call%d (Js.handle h) "%s"%s' % (
        len(args), me['name'], ''.join(' %s_j' % n for n, _, _ in args))
    ret_out(a, rt, rk, call, rt)
    # a GENERIC sibling for the data-carrying form: pass any pinnable
    # array directly — pin scoped around the call
    raws = [n for n, t, k in args if k == 'raw']
    if len(raws) == 1 and rk == 'unit' and mname == pascal(me['name']):
        rn = raws[0]
        sig2 = ', '.join(
            ('%s : %s' % (n, "'a[]") if n == rn else '%s : %s' % (n, t))
            for n, t, _ in args)
        a('    member x.%s (%s) : unit when Unmanaged<\'a> =' % (mname, sig2))
        a('        let %s_p = Array.pin %s' % (rn, rn))
        for n, t, k in args:
            if n == rn:
                a('        let %s_j = Js.viewU8 %s_p (Array.byteSize %s)' % (n, n, n))
            elif k.startswith('seq:'):
                a('        let %s_j = Js.newArr ()' % n)
                a('        for si in 0 .. Array.length %s - 1 do Js.push %s_j (%s)'
                  % (n, n, arg_in('', k[4:], '%s.[si]' % n)))
            else:
                a('        let %s_j = %s' % (n, arg_in(t, k, n)))
        a('        %s |> ignore' % call)
        a('        Array.unpin %s |> ignore' % rn)

def emit_gl(model):
    handles = set(n for n in model['interfaces']
                  if n.startswith('WebGL') and not n.endswith('RenderingContext')
                  and 'ContextBase' not in n and 'Overloads' not in n and n != 'WebGLObject')
    L = []
    a = L.append
    a('// GENERATED by tools/webgl-gen.py from the Khronos WebGL IDLs — do not')
    a('// edit. One real GLenum with every constant at its true value; handles')
    a('// are int-handle classes over the shared JS registry. Browser-only.')
    a('module WebGl')
    a('')
    # GLenum: every const from every interface, deduped by name
    seen = {}
    for iname, iface in model['interfaces'].items():
        for c in iface['consts']:
            v = int(c['value'], 0)
            # negative constants (TIMEOUT_IGNORED : GLint64 = -1) are not
            # GLenum values — they stay off the enum
            if c['name'] not in seen and 0 <= v <= 0x7FFFFFFF:
                seen[c['name']] = v
    a('type GLenum =')
    for n, v in seen.items():
        a('    | %s = %d' % (pascal(n.lower()), v))
    a('')
    # handle classes + contexts in one chain
    first = True
    def hdr(name, suffix):
        nonlocal first
        kw = 'type' if first else 'and'
        first = False
        return '%s %s%s' % (kw, name, suffix)
    for h in sorted(handles):
        a(hdr(h, '(h : int) ='))
        a('    member x.H : int = h')
        a('')
    for ctx, sources in [('WebGLRenderingContext', ['WebGLRenderingContextBase', 'WebGLRenderingContextOverloads', 'WebGLRenderingContext']),
                         ('WebGL2RenderingContext', ['WebGLRenderingContextBase', 'WebGL2RenderingContextBase', 'WebGL2RenderingContextOverloads', 'WebGL2RenderingContext'])]:
        a(hdr(ctx, '(h : int) ='))
        a('    member x.H : int = h')
        # group same-name overloads; the DATA-carrying form (a raw/view
        # parameter) owns the plain name — that is the form samples write —
        # and the rest take occurrence suffixes (Name2, Name3)
        groups = {}
        order = []
        for srcn in sources:
            iface = model['interfaces'].get(srcn)
            if not iface: continue
            for me in iface['methods']:
                if me['name'] not in groups:
                    groups[me['name']] = []
                    order.append(me['name'])
                groups[me['name']].append(me)
        flat = []
        for nm in order:
            g = groups[nm]
            def dataish(me):
                return any(gl_type(model, handles, ar['type'])[1] == 'raw' for ar in me['args'])
            g = sorted(g, key=lambda me: (0 if dataish(me) else 1))
            for idx, me in enumerate(g):
                flat.append((pascal(nm) + ('' if idx == 0 else str(idx + 1)), me))
        emitted = set()
        for mname, me in flat:
            if True:
                if mname in emitted: continue
                emitted.add(mname)
                emit_method(a, model, handles, mname, me)
        # typed extension accessors: getExtension by its registry name,
        # null (unsupported) as None
        for en in model['extensions']:
            a('    member x.Get%s () : option<%s> =' % (en, en))
            a('        let e = Js.call1 (Js.handle h) "getExtension" (Js.ofString "%s")' % en)
            a('        if Js.toBool e then')
            a('            let r = Js.register e')
            a('            let w = %s r' % en)
            a('            Js.watch (box w) r')
            a('            Some w')
            a('        else None')
        a('')
    # extension objects: one class each, methods verbatim from the registry
    for en in model['extensions']:
        iface = model['interfaces'][en]
        a(hdr(en, '(h : int) ='))
        a('    member x.H : int = h')
        for me in iface['methods']:
            emit_method(a, model, handles, pascal(me['name']), me)
        a('')
    a('and Marshal =')
    a('    static member GLenumOf (v : int) : GLenum = unbox (box v)')
    a('')
    for h in sorted(handles):
        a('let Wrap%s (hh : int) : %s = %s hh' % (h, h, h))
    a('let WrapWebGLRenderingContext (hh : int) : WebGLRenderingContext = WebGLRenderingContext hh')
    a('let WrapWebGL2RenderingContext (hh : int) : WebGL2RenderingContext = WebGL2RenderingContext hh')
    return '\n'.join(L) + '\n'

if __name__ == '__main__':
    model = parse_all()
    out = emit_gl(model)
    open('stdlib/webgl.fpp', 'w').write(out)
    print('stdlib/webgl.fpp written:', out.count('\n'), 'lines')
