(module
  ;; generic reflection ABI
  (import "js" "get"     (func $get     (param externref externref) (result externref)))
  (import "js" "set"     (func $set     (param externref externref externref)))
  (import "js" "invoke1" (func $invoke1 (param externref externref externref) (result externref)))
  (import "js" "num"     (func $num     (param f64) (result externref)))
  (import "js" "toNum"   (func $toNum   (param externref) (result f64)))
  (import "js" "str"     (func $str     (param i32) (result externref)))
  ;; dedicated imports: one per operation, the other end of the design space
  (import "dom" "create" (func $create (param externref externref) (result externref)))
  (import "dom" "text"   (func $text   (param externref externref)))
  (import "dom" "append" (func $append (param externref externref)))

  ;; property names live in globals: interned once at startup, so a call site
  ;; pays no crossing to name the thing it is touching
  (global $nCreate (mut externref) (ref.null extern))
  (global $nDiv    (mut externref) (ref.null extern))
  (global $nText   (mut externref) (ref.null extern))
  (global $nItem   (mut externref) (ref.null extern))
  (global $nClass  (mut externref) (ref.null extern))
  (global $nRow    (mut externref) (ref.null extern))
  (global $nAppend (mut externref) (ref.null extern))
  (global $nCount  (mut externref) (ref.null extern))
  (func (export "initNames")
    (global.set $nCreate (call $str (i32.const 0)))
    (global.set $nDiv    (call $str (i32.const 1)))
    (global.set $nText   (call $str (i32.const 2)))
    (global.set $nItem   (call $str (i32.const 3)))
    (global.set $nClass  (call $str (i32.const 4)))
    (global.set $nRow    (call $str (i32.const 5)))
    (global.set $nAppend (call $str (i32.const 6)))
    (global.set $nCount  (call $str (i32.const 7))))

  ;; build n elements through get/set/invoke only
  (func (export "buildGeneric") (param $doc externref) (param $parent externref) (param $n i32)
    (local $i i32) (local $el externref)
    (block $done (loop $go
      (br_if $done (i32.ge_s (local.get $i) (local.get $n)))
      (local.set $el (call $invoke1 (local.get $doc) (global.get $nCreate) (global.get $nDiv)))
      (call $set (local.get $el) (global.get $nText) (global.get $nItem))
      (call $set (local.get $el) (global.get $nClass) (global.get $nRow))
      (drop (call $invoke1 (local.get $parent) (global.get $nAppend) (local.get $el)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go))))

  ;; the same, through purpose-built imports
  (func (export "buildDirect") (param $doc externref) (param $parent externref) (param $n i32)
    (local $i i32) (local $el externref)
    (block $done (loop $go
      (br_if $done (i32.ge_s (local.get $i) (local.get $n)))
      (local.set $el (call $create (local.get $doc) (global.get $nDiv)))
      (call $text (local.get $el) (global.get $nItem))
      (call $append (local.get $parent) (local.get $el))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go))))

  ;; property traffic only: read a number, add one, write it back
  (func (export "propLoop") (param $o externref) (param $n i32) (result f64)
    (local $i i32) (local $v f64)
    (block $done (loop $go
      (br_if $done (i32.ge_s (local.get $i) (local.get $n)))
      (local.set $v (call $toNum (call $get (local.get $o) (global.get $nCount))))
      (call $set (local.get $o) (global.get $nCount) (call $num (f64.add (local.get $v) (f64.const 1))))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go)))
    (call $toNum (call $get (local.get $o) (global.get $nCount))))

  ;; a pure-wasm loop of the same shape, for the floor
  (func (export "pureLoop") (param $n i32) (result f64)
    (local $i i32) (local $v f64)
    (block $done (loop $go
      (br_if $done (i32.ge_s (local.get $i) (local.get $n)))
      (local.set $v (f64.add (local.get $v) (f64.const 1)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $go)))
    (local.get $v))
)
