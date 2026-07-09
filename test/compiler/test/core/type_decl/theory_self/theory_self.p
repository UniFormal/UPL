theory A {
  type tp
  val x: tp
}

val x = A { type tp = A, x = A { type tp = int, x = 17 + 2 } }