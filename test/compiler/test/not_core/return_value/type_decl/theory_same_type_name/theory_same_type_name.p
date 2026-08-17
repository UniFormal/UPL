theory A {
  type tp
  val y: tp
}

theory B {
  type tp
  val z: tp
}

val x = A { type tp = B, y = B { type tp = int, z = 17 - 2 } }