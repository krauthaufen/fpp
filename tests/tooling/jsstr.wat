(module
  (import "wasm:js-string" "length" (func $length (param externref) (result i32)))
  (import "wasm:js-string" "concat" (func $concat (param externref externref) (result (ref extern))))
  (func (export "len") (param externref) (result i32) (call $length (local.get 0)))
  (func (export "cat") (param externref externref) (result externref) (call $concat (local.get 0) (local.get 1)))
)
