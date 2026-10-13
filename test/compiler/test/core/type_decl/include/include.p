theory A {
  type tp
  val x: tp
}

theory B {
  include A
  type tp2
  type tp = int
  val y: tp2
  val z: tp
}

val inst_int = B { type tp2 = int, x = 13, y = 12, z = 3 }
val inst_bool = B { type tp2 = bool, x = 5, y = true, z = 2 }