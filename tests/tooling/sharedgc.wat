(module
  (type $s (shared (struct (field i32))))
  (func (export "mk") (result (ref null $s)) (struct.new $s (i32.const 1)))
)
