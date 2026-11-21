theory B {
  b: int = 4
  c: int
}

theory A {
  a: int = 3
  b = B { c = a + 2 }
  c = b.b + 1 + b.c
  d: int
}

inst = A { d = 5 }