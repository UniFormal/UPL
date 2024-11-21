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
  even = x -> if (x == 0) true else if (x>0) odd(x-1) else odd(-x-1)
  odd = x -> x == 1 | even(x-1)

  id = x -> x
  id0 = id(0)

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

module Algebra {
  class Carrier {
    type U
  }
  class Magma {
    include Carrier
    op: U -> U -> U
  }
  class Monoidal {
    include Magma
    e: U
  }
  intAdd = Magma {type U = int, op = x -> y -> x+y}
  intMult = Magma {type U = int, op = x -> y -> x*y}
  class BiMagma {
    include Carrier
    add  : Magma {type U = U}
    mult : Magma {type U = U}
  }

  module AI {
    class TransitionSystem {
      type state
      type action
      transitions: (state,action) -> state -> bool
      reachable: (state, [action], state) -> bool
      applicable = (s,a) -> exists x. transitions(s,a)(x)
    }
    class Deterministic {
      include TransitionSystem
      transition: (state,action) -> state
      transitions = (s,a) -> x -> transition(s,a) == x
    }
    class SearchProblem {
      include TransitionSystem
      initials: state -> bool
      goals:    state -> bool
      solution: [action] -> bool = as -> exists i,g. initials(i) & reachable(i,as,g) & goals(g)
    }
    class FullyObservable {
      include SearchProblem
      initial: state
      initials = x -> initial == x
    }
    class Cost {
      include TransitionSystem
      cost: action -> rat
    }
    class DefaultCost {
      include Cost
      cost = a -> 1
    }

    class SearchStrategy {}

    treeSearch: (SearchProblem, SearchStrategy) -> bool = (p,y) -> {
      var fringe: [p.state] = []
      while (fringe != []) {

      }
      false
    }
  }
}