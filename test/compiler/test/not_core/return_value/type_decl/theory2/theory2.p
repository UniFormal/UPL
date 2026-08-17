theory A {
  type tp
  val z: tp
}

theory B {
  val y: A
}

val x = B { y = A { type tp = int, z = 13 * 2 } }