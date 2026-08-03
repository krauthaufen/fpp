// Replaces FSharp.Data.Adaptive's Equality.fs.
//
// The original routes every hash and comparison through a swappable
// IEqualityProvider whose default reaches .NET runtime services —
// `Unchecked.hash`, `EqualityComparer<'T>.Default`, RuntimeHelpers — none
// of which exist here. F++'s `hash` and `=` ARE the structural comparison
// those services provide for the types this library stores, so the
// providers collapse to them. The provider INDIRECTION is kept: the
// adaptive tests call SetProvider, and the shape of the API is part of the
// library's surface.

type IEqualityProvider =
    abstract member GetEqualityComparer<'T> : unit -> IEqualityComparer<'T>

type DefaultEqualityComparer private() =
    static let mutable created = 0

    static let unchecked =
        { new IEqualityProvider with
            member x.GetEqualityComparer<'T>() =
                { new IEqualityComparer<'T> with
                    member __.GetHashCode(o : 'T) = hash o
                    member __.Equals(l : 'T, r : 'T) = l = r
                }
        }

    static let mutable defaultCreator = unchecked
    static member Unchecked = unchecked
    /// structural here, exactly as Unchecked: the runtime services the
    /// original distinguishes do not exist to differ
    static member System = unchecked
    static member Shallow = unchecked

    /// handle with care!!
    static member SetProvider(creator : IEqualityProvider) =
        if not (System.Object.ReferenceEquals(defaultCreator, creator)) then
            if created > 0 then failwith "cannot only set default equality before first use"
            defaultCreator <- creator

    static member internal GetEqualityComparer<'T>() =
        created <- 1
        defaultCreator.GetEqualityComparer<'T>()

type DefaultEqualityComparer<'T> private() =
    /// computed per ACCESS, not cached in a static let: a generic class's
    /// static initializer runs once at program start with 'T unresolved
    /// (see DIVERGENCES.md on generic values), and the comparers here are
    /// stateless anyway
    static member Instance = DefaultEqualityComparer.GetEqualityComparer<'T>()

module DefaultDictionary =
    let inline create<'Key, 'Value> () =
        Dictionary<'Key, 'Value>()

module DefaultHashSet =
    let inline create<'T> () =
        MutableHashSet<'T>()

module DefaultEquality =
    let inline hash (value : 'T) =
        DefaultEqualityComparer<'T>.Instance.GetHashCode(value)

    let inline equals (a : 'T) (b : 'T) =
        DefaultEqualityComparer<'T>.Instance.Equals(a, b)

/// identity comparison. `hash` on a class that declares no GetHashCode is
/// the identity hash already, and reference equality is spelled the same
/// way the original spells it.
type ReferenceEqualityComparer<'T> private() =
    static member Instance =
        { new IEqualityComparer<'T> with
            member __.GetHashCode(o : 'T) = hash o
            member __.Equals(l : 'T, r : 'T) = System.Object.ReferenceEquals(l, r)
        }

module ReferenceHashSet =
    let inline create<'T> () =
        MutableHashSet<'T>()
