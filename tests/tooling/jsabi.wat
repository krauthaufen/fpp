;; The whole of JS through a fixed, small set of primitives.
;; Nothing DOM-specific is imported: no createElement, no appendChild.
(module
  (import "js" "global"    (func $global    (param externref) (result externref)))          ;; globalThis.<name>
  (import "js" "get"       (func $get       (param externref externref) (result externref)));; o[k]
  (import "js" "set"       (func $set       (param externref externref externref)))         ;; o[k] = v
  (import "js" "invoke1"   (func $invoke1   (param externref externref externref) (result externref)))
  (import "js" "invoke2"   (func $invoke2   (param externref externref externref externref) (result externref)))
  (import "js" "construct1"(func $construct1(param externref externref) (result externref)));; new C(a)
  (import "js" "num"       (func $num       (param f64) (result externref)))                ;; number in
  (import "js" "toNum"     (func $toNum     (param externref) (result f64)))                ;; number out
  (import "js" "func"      (func $func      (param funcref) (result externref)))            ;; wasm fn -> JS callback
  (import "js" "str"       (func $str       (param i32) (result externref)))                ;; interned literals
  (global $clicks (mut i32) (i32.const 0))

  ;; a plain wasm function, handed to JS as an event listener
  (func $onClick (param externref)
    (global.set $clicks (i32.add (global.get $clicks) (i32.const 1))))
  (elem declare func $onClick)

  (func (export "clicks") (result i32) (global.get $clicks))

  (func (export "build")
    (local $doc externref) (local $body externref) (local $btn externref) (local $date externref)
    ;; document = globalThis.document
    (local.set $doc (call $global (call $str (i32.const 0))))
    ;; document.body
    (local.set $body (call $get (local.get $doc) (call $str (i32.const 1))))
    ;; document.createElement("button")
    (local.set $btn (call $invoke1 (local.get $doc) (call $str (i32.const 2)) (call $str (i32.const 3))))
    ;; btn.textContent = "made through get/set/invoke"
    (call $set (local.get $btn) (call $str (i32.const 4)) (call $str (i32.const 5)))
    ;; btn.id = "made"
    (call $set (local.get $btn) (call $str (i32.const 6)) (call $str (i32.const 7)))
    ;; btn.addEventListener("click", <wasm function>)
    (drop (call $invoke2 (local.get $btn) (call $str (i32.const 8)) (call $str (i32.const 9))
                         (call $func (ref.func $onClick))))
    ;; body.appendChild(btn)
    (drop (call $invoke1 (local.get $body) (call $str (i32.const 10)) (local.get $btn)))
    ;; `new` works too: new Date(0).getUTCFullYear() -> 1970
    (local.set $date (call $construct1 (call $global (call $str (i32.const 11))) (call $num (f64.const 0))))
    (call $set (local.get $btn) (call $str (i32.const 12))
       (call $num (call $toNum (call $invoke1 (local.get $date) (call $str (i32.const 13)) (call $str (i32.const 14))))))
  )
)
