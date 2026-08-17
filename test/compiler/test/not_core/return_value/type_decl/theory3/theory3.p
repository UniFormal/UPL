theory A {
  type tp
  val z: tp
}

val y: A = A { type tp = int, z = 13 * 2 }