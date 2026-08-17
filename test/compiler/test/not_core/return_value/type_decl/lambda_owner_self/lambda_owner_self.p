theory A {
  type tp
  val x: tp
}

lambda = () -> {
  A { type tp = int, x = 20 }
}

val outer = A { type tp = A, x = lambda() }
