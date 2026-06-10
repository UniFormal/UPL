theory B {
  b: int = 4
}

theory A {
  a: int = 3
  b = B { }
  c = b.b + 1
}

inst = A { }