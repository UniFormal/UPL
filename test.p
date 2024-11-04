module M {
  class Person {
    name: string
    age: int
  }
  class Gendered {
    include Person
    male: bool
    age = 5
    address = (if (male) "Mr" else "Mrs") + " " + name
  }
  odd: int -> bool
  even = x -> if (x == 0) true else if (x>0) odd(x-1) else odd(-x-1)
  id = x -> x
  id0 = id(0)
  odd = x -> x == 1 | even(x-1)
  foreach : ([int], int -> ()) -> () = (l,f) -> for (i in l) f(i)
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = [f(x)] + r}
    r
  }
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }
  test = {
    sum([1,2,3])
  }
}
main = .M.test
