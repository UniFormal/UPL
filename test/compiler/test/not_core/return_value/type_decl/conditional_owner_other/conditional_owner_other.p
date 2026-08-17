theory A {
  type tp
  val x: tp
}

theory B {
  type tp
  val x: tp
}

val left = A { type tp = int, x = 11 }
val right = A { type tp = int, x = 22 }
val outer = A { type tp = A, x = if (true) left else right }