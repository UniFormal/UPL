module Mutable {
  theory A {
    mutable a: int = 1
    x = {
      a = 3
    }
    inc = () -> {
      a = a + 1
    }
  }

  test = {
    val x = A { }
    ASSERT(x.a, 3)
    x.a = 5
    ASSERT(x.a, 5)
    x.a = x.a + 1
    ASSERT(x.a, 6)
    x.inc()
    ASSERT(x.a, 7)
  }
}

