module Fpp.Query

open Fpp.Prelude

// Salsa-style incremental query engine, minimal edition.
//
// The database holds inputs (set explicitly, bumping the revision) and
// derived queries (memoized computations). While a derived query runs, every
// input or query it reads is recorded as a dependency. On later reads a
// derived value is reused if no dependency changed since it was computed;
// recomputation that produces an equal value keeps the old ChangedAt, so
// downstream queries are not invalidated (early cutoff).
//
// The LSP server and the batch compiler are both clients of one Db — that is
// the architectural bet of the whole project, made here, first.

type Revision = int

type QueryKey = string * string

type private Entry =
    { mutable Value : obj
      mutable Deps : QueryKey list
      /// revision at which Value was (re)computed
      mutable ComputedAt : Revision
      /// revision up to which Value is known to be valid
      mutable VerifiedAt : Revision
      /// revision at which Value last actually changed
      mutable ChangedAt : Revision
      /// None for inputs
      mutable Compute : (unit -> obj) option }

type Db() =
    let table : Dict<QueryKey, Entry> = dictNew ()
    let mutable revision : Revision = 0
    let mutable depStack : Vec<QueryKey> list = []
    let mutable computeCount = 0

    member _.Revision = revision
    /// Number of derived-query executions (test/telemetry hook).
    member _.ComputeCount = computeCount

    member private _.Record (qk : QueryKey) : unit =
        match depStack with
        | top :: _ -> vecAdd top qk
        | [] -> ()

    member _.SetInput (query : string) (key : string) (value : obj) : unit =
        let qk = (query, key)
        match dictTryFind table qk with
        | Some e ->
            if not (obj.Equals (e.Value, value)) then
                revision <- revision + 1
                e.Value <- value
                e.ComputedAt <- revision
                e.VerifiedAt <- revision
                e.ChangedAt <- revision
        | None ->
            revision <- revision + 1
            dictSet table qk
                { Value = value; Deps = []; ComputedAt = revision
                  VerifiedAt = revision; ChangedAt = revision; Compute = None }

    member this.GetInput (query : string) (key : string) : obj =
        let qk = (query, key)
        this.Record qk
        match dictTryFind table qk with
        | Some e -> e.Value
        | None -> failwith ("query engine: unset input " + query + "/" + key)

    member private this.Recompute (e : Entry) : unit =
        let deps = vecNew<QueryKey> ()
        depStack <- deps :: depStack
        computeCount <- computeCount + 1
        let v =
            match e.Compute with
            | Some f -> f ()
            | None -> e.Value
        depStack <- List.tail depStack
        e.Deps <- vecToList deps
        e.ComputedAt <- revision
        e.VerifiedAt <- revision
        if not (obj.Equals (v, e.Value)) then
            e.Value <- v
            e.ChangedAt <- revision

    /// Bring an entry up to date for the current revision.
    member private this.Ensure (qk : QueryKey) : Entry =
        match dictTryFind table qk with
        | None -> failwith "query engine: dangling dependency"
        | Some e ->
            if e.VerifiedAt <> revision then
                match e.Compute with
                | None -> e.VerifiedAt <- revision
                | Some _ ->
                    let depChanged =
                        e.Deps |> List.exists (fun d -> (this.Ensure d).ChangedAt > e.ComputedAt)
                    if depChanged then this.Recompute e
                    else e.VerifiedAt <- revision
            e

    member this.Memo (query : string) (key : string) (compute : unit -> obj) : obj =
        let qk = (query, key)
        this.Record qk
        match dictTryFind table qk with
        | Some e ->
            e.Compute <- Some compute
            (this.Ensure qk).Value
        | None ->
            let e =
                { Value = null; Deps = []; ComputedAt = -1
                  VerifiedAt = -1; ChangedAt = -1; Compute = Some compute }
            dictSet table qk e
            this.Recompute e
            e.Value

    member this.MemoT<'a> (query : string) (key : string) (compute : unit -> 'a) : 'a =
        unbox<'a> (this.Memo query key (fun () -> box (compute ())))
