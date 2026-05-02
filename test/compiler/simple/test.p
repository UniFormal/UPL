module Data {
  theory A {
    a: int = 3 + 5
    b: int
  }
  theory B {
    include A
    b: int = 69
    c: int
  }
  test3: B = B { c = 2 }
  a = test3.a
}