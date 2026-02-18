module Data {
  theory Test {
    x: int
    s: string
  }

  theory Test2 {
    k: Test
    a: int
    g: comp
  }

  test1: Test = Test {x = 2, s = "hello"}

  objects: list[Test] // = read("data.pd")

  test = test1.x == 2
}