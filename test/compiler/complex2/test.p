module Data {
  theory T1 {
    y: int
    x: int = 3 + 66
  }
  theory T2 {
    x: int
  }
  theory T3 {
    include T1
    include T2
    x: int
    y: int = 65
    z: int = 5
    s: int
  }
  theory T4 {
    include T1
    include T3
    a: int
    b: int
    x: int
  }
  test3: T3 = T3 { s = 12 }
  a = test3.x // 3
//  test2: T2 = test3
//  test1: T1 = test3
//  a = test1.x // 3
//  b = test2.x // 3
//  c = test3.x // 3//

//  d = test1.z // unknown identifier z while checking z
//  e = test2.z // unknown identifier z while checking z
//  f = test3.z // 5//

//  g = test1.y // 65
//  h = test2.y // unknown identifier y while checking y
//  i = test3.y // 65

}