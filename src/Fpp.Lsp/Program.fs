module Fpp.Lsp.Program

open Fpp

[<EntryPoint>]
let main _argv =
    let stdin = System.Console.OpenStandardInput()
    let stdout = System.Console.OpenStandardOutput()
    let server = Server.Server(Workspace())
    let mutable go = true
    while go do
        match Protocol.readMessage stdin with
        | None -> go <- false
        | Some msg ->
            for reply in server.Handle msg do
                Protocol.writeMessage stdout reply
            if server.ExitRequested then go <- false
    0
