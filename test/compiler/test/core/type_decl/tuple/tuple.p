theory A {
  type tp
  val x: tp
}

val inst_iib = A { type tp = (int, int, bool), x = (4, 3, false) }
val inst_iii = A { type tp = (int, int, int), x = (1, 2, 3) }