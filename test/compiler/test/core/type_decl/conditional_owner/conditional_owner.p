theory A {
  type tp
  val x: tp
}

val outer = A { type tp = int, x = if (false) 13 else 11 }