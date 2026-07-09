theory A {
  type tp
  val x: tp
}

theory B {
  include A
  type tp2
  val y: tp2
  val z: tp
}

val inst1 = B { type tp = bool, type tp2 = int, x = false, y = 12, z = true }
val inst2 = B { type tp = int, type tp2 = bool, x = 5, y = true, z = 2 }