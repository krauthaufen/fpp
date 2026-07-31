;; Can wasm hold and pass JS objects directly, with no integer handle table?
;; Every DOM operation is an IMPORT; the objects themselves travel as externref.
(module
  (import "dom" "createElement" (func $createElement (param externref) (result externref)))
  (import "dom" "setText"       (func $setText (param externref externref)))
  (import "dom" "appendChild"   (func $appendChild (param externref externref)))
  (import "dom" "literal"       (func $literal (param i32) (result externref)))

  ;; a struct FIELD holding a JS object: no table, no index
  (type $box (struct (field $node (mut externref))))

  (func (export "build") (param $parent externref)
    (local $div externref) (local $b (ref $box))
    ;; document.createElement("div")
    (local.set $div (call $createElement (call $literal (i32.const 0))))
    ;; stash the JS object inside a wasm-GC struct, then read it back
    (local.set $b (struct.new $box (local.get $div)))
    (call $setText (struct.get $box $node (local.get $b)) (call $literal (i32.const 1)))
    (call $appendChild (local.get $parent) (struct.get $box $node (local.get $b)))
  )
)
