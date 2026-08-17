theory A {
  mutable a: int = 1
}

inst = A { }

test = {
  inst.a = inst.a + 1
}