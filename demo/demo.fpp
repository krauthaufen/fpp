module Demo

extern let jsRect : int -> int -> int -> int
extern let jsStatus : string -> int

let width = 129
let rows = 64

let drawRow (y : int) (cells : int[]) =
    let mutable x = 0
    while x < width do
        let d = if cells.[x] = 1 then jsRect x y 1 else 0
        x <- x + 1
    0

let stepRow (cur : int[]) =
    let next = Array.create width 0
    let mutable i = 1
    while i < width - 1 do
        let v = cur.[i - 1] + cur.[i + 1]
        next.[i] <- (if v = 1 then 1 else 0)
        i <- i + 1
    next

let runAutomaton () =
    let start = Array.create width 0
    let z = start.[width / 2] <- 1
    let mutable cur = start
    let mutable y = 0
    while y < rows do
        let d = drawRow y cur
        cur <- stepRow cur
        y <- y + 1
    0

let hello = print "rule 90, computed by F++"
let go = runAutomaton ()
let s = jsStatus ("F++ -> JS string: " + "rendered " + "on canvas")
