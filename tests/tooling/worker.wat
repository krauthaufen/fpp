;; Each worker instantiates this over the SAME shared memory.
(module
  (import "env" "mem" (memory 1 1 shared))
  (func (export "hammer") (param $addr i32) (param $n i32)
    (local $i i32)
    (block $d (loop $g
      (br_if $d (i32.ge_s (local.get $i) (local.get $n)))
      (drop (i32.atomic.rmw.add (local.get $addr) (i32.const 1)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $g))))
  ;; a non-atomic version, to show the difference is real
  (func (export "hammerRacy") (param $addr i32) (param $n i32)
    (local $i i32)
    (block $d (loop $g
      (br_if $d (i32.ge_s (local.get $i) (local.get $n)))
      (i32.store (local.get $addr) (i32.add (i32.load (local.get $addr)) (i32.const 1)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $g))))
)
