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
  sum = (l: list[int]) -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }
}
main = M.sum(list(1,2,3))
