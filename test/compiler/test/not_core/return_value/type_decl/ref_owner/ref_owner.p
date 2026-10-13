theory A {
  type tp
  val x: tp
}

val inner = A { type tp = int, x = 11 + 2 }
val outer = A { type tp = A, x = inner }
