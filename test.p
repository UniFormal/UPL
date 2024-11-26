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

  foreach : ([int], int -> ()) -> () = (l,f) -> for (i in l) f(i)
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = [f(x)] + r}
    r
  }
  map2:_
  map2 = (l: [int]) -> f -> {
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

  factorial: _
  factorial = (x:int) -> {
    if (x <= 0) return 1
    x * factorial(x-1)
  }

  test = {
    sum([1,2,3]) == 6 &
    factorial(3) == 6
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
}

module AI {
    type state = int
    class TransitionSystem {
      type action
      enumAllActions: [action]
      transitions: (state,action) -> [state]
      applicable = (s,a) -> exists x. x in transitions(s,a)
      reachable:_
      reachable = (f:state, path: [action], t:state) -> path match {
        [] -> f == t
        a -: as -> exists x. x in transitions(f,a) & reachable(x,as,t)
      }
    }
    class Deterministic {
      include TransitionSystem
      transition: (state,action) -> state?
      transitions = (s,a) -> transition(s,a)
    }
    class SearchProblem {
      include TransitionSystem
      initials: [state]
      goals:    state -> bool
      solution: [action] -> bool = as -> exists i,g. i in initials & reachable(i,as,g) & goals(g)
    }
    class FullyObservable {
      include SearchProblem
      initial: state
      initials = [initial]
    }
    class Cost {
      include TransitionSystem
      cost: action -> rat
    }
    class DefaultCost {
      include Cost
      cost = a -> 1
    }

    class Node {
      label: state
      parent: Node
    }

    class SearchStrategy {
       type Fringe
       init: [state] -> Fringe
       empty: Fringe -> bool
       insert: Fringe -> (Node,state) -> ()
       takeNext: Fringe -> Node
    }

    treeSearch: (SearchProblem, SearchStrategy) -> Node? = (prob,strat) -> {
      val fringe: strat.Fringe = strat.init(prob.initials)
      while (!strat.empty(fringe)) {
         val node = strat.takeNext(fringe)
         if (prob.goals(node.label)) return node?
         else
           for (a in prob.enumAllActions)
             for (s in prob.transitions(node.label, a))
               strat.insert(fringe)(node, s)
      };
      ?
    }
}