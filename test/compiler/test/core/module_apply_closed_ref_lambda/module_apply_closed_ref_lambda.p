theory A {
  sqr : (int) -> int = (x: int) -> x * x
  a = sqr(4)
}

inst = A { }