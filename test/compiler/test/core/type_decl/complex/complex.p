type bl = bool

theory A {
  type tp
  val x: bl
  val y: tp
  val z: int = 8
  val a: (bl, bl)
  val b: (tp, bl)
}

val inst = A { type tp = int, x = true, y = 15, a = (true, false), b = (5, true) }
val inst2 = A { type tp = bool, x = true, y = false, a = (false, true), b = (true, false) }