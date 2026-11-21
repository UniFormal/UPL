theory A {
  sqr : (int) -> int = (x: int) -> x * x
  f : (int) -> int
}

inst = A { f = (x: int) -> x + 1 }