# Generic class `'a[]` field reads Length = 0 (pre-existing)

A generic class whose field is `'a[]` reads that field's `.Length` as 0, even
though element access on the same field works. Reproduces under `--linear` and
`--gc`, for both `int` and `string` elements; a CONCRETE `int[]` field is fine.

```fsharp
type Bg<'a>() =
    let mutable items : 'a[] = Array.zeroCreate 5
    member x.Len = items.Length     // → 0, should be 5
    member x.Get = items.[0]        // works
```

This is why `ResizeArray`/`Dictionary` hang/OOB under WasmLin: `Reserve`'s
`while cap < count+n do cap <- cap*2` spins forever on `cap = items.Length*2 = 0`.

PRE-EXISTING: reproduces at f8c3ef6 (predates the raw-int / inline-scalar work);
`ResizeArray.Add` already hangs there. The self-host does NOT depend on these
collections (f8c3ef6 ran fully without them), so this is deferred — it is a
separate defect from the enumerator `indirect call type mismatch` self-host blocker.
