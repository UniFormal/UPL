theory A {
  a = 10
  f : (int) -> int = (x: int) -> { val b = 3; x + a + b }
}

inst = A { }