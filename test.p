module M {
  class Person {
    name: string
    age: int
  }
  class Gendered {
    include Person
    male: bool
    age = 5
    address = (if male "Mr" else "Mrs") + " " + name
  }
  odd: int -> bool
  even = (x: int) -> if x == 0 true else if x>0 odd(x-1) else odd(-x-1)
  odd = (x) -> x == 1 | even(x-1)
  foreach : (list[int], int -> ()) -> () = (l,f) -> for i in l f(i)
  map = (l: list[int]) -> (f: int -> int) -> {
    var r: list[int] = list()
    for x in l {r = list(f(x)) + r}
    r
  }
  sum = (l: list[int]) -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }
  test = {
   sum(list(1,2,3))
}
main = M.test
