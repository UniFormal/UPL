theory A {
  type tp
  val x: tp
}

theory B {
  val x: A
}

val x = B { x = A { type tp = int, x = 13 * 2 } }