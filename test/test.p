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

  odd: _
  even = x -> x == 0 | if (x>0) odd(x-1) else odd(-x-1)
  odd = x -> if (x == 0) false else even(x-1)

  id = x -> x
  id0 = id(0)

  foreach : ([int], int -> ()) -> () = (l,f) -> {for (i in l) f(i); ()}
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = f(x) -: r}
    r
  }
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      h-:t -> f(h)-:map2(t)(f)
    }
  }
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }

  ac = { val abc = ["a", "b", "c"];
         (val a) -: _ = abc;
         _ :- (val c) = abc;
         (a,c)
        }


  factorial: _
  factorial = (x:int) -> {
    if (x <= 0) return 1
    x * factorial(x-1)
  }

  deepBinding1 = {factorial(factorial(val n = 3)); n+1} == 4

  test = {
    M.sum([1,2,3]) == 6 &
    M.factorial(3) == 6 &
    M.map2([1,2,3])(x -> x+1) == [2,3,4] &
    deepBinding1 &
    ac == ("a","c")
  }
}