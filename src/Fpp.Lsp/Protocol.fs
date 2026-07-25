module Fpp.Lsp.Protocol

// LSP base-protocol framing: `Content-Length: N\r\n\r\n<N bytes of JSON>`.
// The LSP host is deliberately outside the bootstrap seam — it is tooling
// host code and may use the full BCL.

open System.IO
open System.Text
open System.Text.Json.Nodes

let private readLine (input : Stream) : string option =
    let sb = StringBuilder()
    let mutable fin = false
    let mutable eof = false
    while not fin do
        match input.ReadByte() with
        | -1 ->
            fin <- true
            eof <- true
        | 10 -> fin <- true                        // '\n'
        | 13 -> ()                                  // '\r'
        | b -> sb.Append(char b) |> ignore
    if eof && sb.Length = 0 then None else Some (sb.ToString())

/// Read one framed JSON-RPC message; None on end of stream.
let readMessage (input : Stream) : JsonNode option =
    let mutable contentLength = -1
    let mutable go = true
    let mutable eof = false
    while go do
        match readLine input with
        | None ->
            go <- false
            eof <- true
        | Some "" -> go <- false
        | Some line ->
            let prefix = "Content-Length:"
            if line.StartsWith prefix then
                contentLength <- int (line.Substring(prefix.Length).Trim())
    if eof || contentLength < 0 then None
    else
        let buf = Array.zeroCreate contentLength
        let mutable read = 0
        let mutable ok = true
        while ok && read < contentLength do
            let k = input.Read(buf, read, contentLength - read)
            if k <= 0 then ok <- false else read <- read + k
        if not ok then None
        else Some (JsonNode.Parse(Encoding.UTF8.GetString buf))

let writeMessage (output : Stream) (msg : JsonNode) : unit =
    let bytes = Encoding.UTF8.GetBytes(msg.ToJsonString())
    let header = Encoding.ASCII.GetBytes(sprintf "Content-Length: %d\r\n\r\n" bytes.Length)
    output.Write(header, 0, header.Length)
    output.Write(bytes, 0, bytes.Length)
    output.Flush()
