theory A {
  mutable a: int = 1
  inc = () -> {
    a = a + 1
  }
}

inst = A { }

test = {
  inst.inc()
}