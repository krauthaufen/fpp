;; A handler with CAPTURED STATE. An F++ lambda is a struct (code + env), not a
;; bare funcref, so JS cannot call it directly: wasm exports one apply function,
;; JS wraps the closure value in a JS function that calls back through it.
(module
  (import "js" "makeCallback" (func $makeCallback (param anyref) (result externref)))
  (import "js" "invoke2"      (func $invoke2 (param externref externref externref externref) (result externref)))
  (import "js" "getNum"       (func $getNum (param externref externref) (result f64)))
  (import "js" "str"          (func $str (param i32) (result externref)))
  (import "js" "global"       (func $global (param externref) (result externref)))
  (import "js" "getRef"       (func $getRef (param externref externref) (result externref)))

  ;; the closure: captured state lives in a wasm-GC struct
  (type $counter (struct (field $label i32) (field $hits (mut i32))))

  (global $c1 (mut (ref null $counter)) (ref.null $counter))
  (global $c2 (mut (ref null $counter)) (ref.null $counter))

  ;; JS calls THIS with the closure it was handed, plus the event
  (func (export "applyCallback") (param $clo anyref) (param $ev externref)
    (local $c (ref $counter))
    (local.set $c (ref.cast (ref $counter) (local.get $clo)))
    ;; captured state and the event, together
    (struct.set $counter $hits (local.get $c)
      (i32.add (struct.get $counter $hits (local.get $c))
               (i32.trunc_f64_s (call $getNum (local.get $ev) (call $str (i32.const 0)))))))

  (func (export "install") (param $a externref) (param $b externref)
    (global.set $c1 (struct.new $counter (i32.const 1) (i32.const 0)))
    (global.set $c2 (struct.new $counter (i32.const 2) (i32.const 0)))
    ;; two listeners, same code, DIFFERENT captured state
    (drop (call $invoke2 (local.get $a) (call $str (i32.const 1)) (call $str (i32.const 2))
                         (call $makeCallback (global.get $c1))))
    (drop (call $invoke2 (local.get $b) (call $str (i32.const 1)) (call $str (i32.const 2))
                         (call $makeCallback (global.get $c2)))))

  (func (export "hits1") (result i32) (struct.get $counter $hits (global.get $c1)))
  (func (export "hits2") (result i32) (struct.get $counter $hits (global.get $c2)))
)
