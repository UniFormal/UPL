module Data {
  theory A {
    a: int = 3 + 5
  }
  theory B {
    include A
    b: int
    a: int
    c: int
    d: int
  }
  theory C {
    include A
    c: int
  }
  theory D {
    include B
    include C
    d: int = 5
  }
  test3: D = D { b = 2, c = 3 }
}