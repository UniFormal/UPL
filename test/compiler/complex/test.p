module Data {
  theory T1 {
    y: int
    x: int = 1
  }
  theory T2 {
    x: int
  }
  theory T3 {
    include T1
    include T2
    x: int
    y: int = 65 + 4
    z: int = 5
    s: int
  }
  test1 = T3 { s = 12 }
}