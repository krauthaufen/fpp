type IShow =
    abstract Show : unit -> string

type Card(n : int) =
    interface IShow with
        member _.Show () = "card:" + string n

type Tag(s : string) =
    interface IShow with
        member _.Show () = "tag:" + s

// a case bounded by an INTERFACE: the value carries its vtable,
// the bound licenses the dispatch in the branch
type Item =
    | Showable of 'a when 'a :> IShow
    | Plain of int

let render (i : Item) : string =
    match i with
    | Showable v -> v.Show ()
    | Plain n -> string n

let items = [ Showable (Card 7); Showable (Tag "x"); Plain 3 ]
for it in items do printfn "%s" (render it)
