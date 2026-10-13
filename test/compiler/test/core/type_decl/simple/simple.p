theory A {
  type tp
  val x: tp
}

val inst_int = A { type tp = int, x = 17 }
val inst_bool = A { type tp = bool, x = true }