(module
  (memory (export "mem") 1 1 shared)
  (func (export "bump") (param i32) (result i32)
    (i32.atomic.rmw.add (local.get 0) (i32.const 1)))
)
