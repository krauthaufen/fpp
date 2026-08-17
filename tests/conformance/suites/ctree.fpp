// Explicit-field classes with several constructors, from dotnet/fsharp
// tests/fsharp/core/members/ctree/test.fsx (a compile-only suite there;
// construction asserts added so both sides RUN the classes too). The
// prefix type-parameter spelling `'a ctree` becomes `ctree<'a>`.
module Core_members_ctree

let mutable ntests = 0
let mutable failures = 0
let test (s : string) (b : bool) : unit =
    ntests <- ntests + 1
    if not b then
        failures <- failures + 1
        printfn "NO: %s" s

type ctree<'a> =
    class
        val isLeaf : bool
        val leafVal : 'a option
        val children : ctree<'a> list

        new (x : 'a) = { isLeaf = true; leafVal = Some x; children = [] }

        new ((dummy : bool), (l : ctree<'a> list)) = { isLeaf = false; leafVal = None; children = l }

        static member MkNode (l : ctree<'a> list) = new ctree<'a>(true, l)
    end

let leaf = new ctree<int>(42)
test "ct1" leaf.isLeaf
test "ct2" (leaf.leafVal = Some 42)
test "ct3" (List.isEmpty leaf.children)

let node = ctree<int>.MkNode [ leaf; new ctree<int>(7) ]
test "ct4" (not node.isLeaf)
test "ct5" (node.leafVal = None)
test "ct6" (List.length node.children = 2)
test "ct7" ((List.item 1 node.children).leafVal = Some 7)

let sleaf = new ctree<string>("hi")
test "ct8" (sleaf.leafVal = Some "hi")

printfn "DONE tests=%d failures=%d" ntests failures
