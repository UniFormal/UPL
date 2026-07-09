theory A {
  type tp
  val x: tp
}

theory B {
  val x: int
}

val x = A { type tp = B, x = B { x = 17 - 2 } }