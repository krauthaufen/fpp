# Witness completeness → full moving GC

GOAL: every generic context knows ref-vs-raw for its type params (a WITNESS
per param, everywhere), so nothing is traced conservatively; then evacuation
comes back on, and pinning is what it should be — per-object (`fpprt_pin`),
temporary, with movement resuming around and after pins.

Today's state (shipped, sound, but compaction OFF): the uniform-word forms
(FK_TAGGED bodies, ref arrays, RANGE roots) are traced conservatively under
mmc because SOME sites hold words of unknown kind. This plan removes the
"unknown" case; the conservative mode then goes entirely.

## Where witnesses already flow (do not rebuild)
- Generic top-level fns: hidden witness param per quantified var
  (`st.FuncWitness`, registered ~13790; callers prepend via `witnessArgs`;
  `emitFuncLow` seeds `ctx.Witness`). Class CTORS are covered (proved: a
  plain generic class ctor mints a witnessed cell).
- Lifted lambdas: enclosing witnesses captured into the closure env
  (`st.LamWits`, `encWits`), reloaded at entry.
- Stamped clones: CONSTANT witnesses (`stampedClassWits` → `constWits`).
- Aggregates: `genWitsOf` per-slot; cons (`lowGenericCons`), cells
  (`lowMkCellW`) select tids at runtime by refMask.

## The gaps (each = a conservative-mode dependency)
1. MEMBERS and vtable impls: excluded from hidden params (dispatch signature
   is fixed) → `ctx.Witness` empty in every member body. THE major gap; the
   Seq combinators' objexpr members mint witness-less `cur`/`acc` cells.
2. obj@ records (objexpr captures): store captures but not the enclosing
   witnesses, so canonical objexpr members can never recover them.
3. Canonical generic arrays: `'a[]` at a raw stamp is FK_REF_ARRAY holding
   raw words; needs runtime tid selection (scalar-vs-ref array) by witness,
   like cons/cells.
4. Residual unconditional `$spush`es of RKGen values (audit; most sites are
   already witness-conditional via ActiveGen/SlottedGen).

## Design: witnesses as PHANTOM TRAILING FIELDS
For a witnessed type (generic class, obj@ record), append fields
`$w0..$wN-1` (one per class param, declared type "?") to its DRecord:
- layouts/offsets/inheritance-prefix/ERecordExt base-copy all fall out of
  the ordinary field machinery — a derived class copies the base segment
  INCLUDING the base's witness fields;
- the ctor supplies them: the ERecord/ERecordExt arms map `$wK` to
  `ctx.Witness[ClassCtorWits[K]]` (the ctor's own hidden params — already
  wired as `witVal`); a stamped ctor's constants ride the same path;
- MEMBERS read them off self: `selfWits` maps receiver `TCon (cn, args)`
  TVar args to the `$wK` field offsets (today it guesses `HDR+4*nf+4*j`;
  change to the phantom fields' real offsets from RecFields order);
- obj@ records get the ENCLOSING fn's quantified vars as their params.
- Scan map: `$w` slots are RKRaw (witness pointers are immortal statics).

## Runtime phase (after the compiler phase is complete and gated)
- Remove `FPPRT_UNIFORM_CONSERVATIVE`: trace_one's conservative branch,
  the pinned-roots range routing, ambiguous-edges at init.
- Evacuation resumes. Verify per-object pinning: `gc_pin_object` sets the
  nofl PINNED metadata bit; `nofl_space_should_evacuate` must skip pinned
  objects (verify + test); EArrayPin/EArrayUnpin semantics — check unpin
  exists and clears the bit, so movement RESUMES for unpinned objects.
- Gate: full battery + adaptive + BinBattery + self-host + shader gates,
  plus a new pin-churn gate (pin, collect, unpin, collect, assert moved).

## Order of work
1. Phantom-field mechanism + WitnessedClasses for generic CLASSES (no
   inherit first, then inherit), ERecord/ERecordExt `$wK` supply, selfWits
   offsets. Gate after each.
2. obj@ records (enclosing-var witnesses as fields), member reading.
3. Witnessed generic arrays (runtime tid).
4. Push-site audit → witness-conditional everywhere.
5. Flip: assert-instead-of-conservative under a build flag; run everything;
   then remove conservative mode + restore evacuation; pin gate.
