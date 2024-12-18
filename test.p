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

module Numbers {
  class Nat {
    type num
    z: num
    s: num -> num
    o = s(z)
    plus: (num,num) -> num
    plus_z: |- forall x. plus(x,z)==x
    plus_s: |- forall x,n. plus(x,s(n))== s(plus(x,n))
    times: (num,num) -> num
    times_z: |- forall x. times(x,z)==z
    times_s: |- forall x,n. times(x,s(n))== plus(times(x,n), x)
    square = x -> times(x,x)
  }
  class Int {
    include Nat
    p: num -> num
    ps: |- forall x. p(s(x)) == x
    sp: |- forall x. s(p(x)) == x

    plus_p: |- forall x,n. plus(x,p(n)) == p(plus(x,n))

    uminus: num -> num
    uminus_z: |- uminus(z) == z
    uminus_s: |- forall n. uminus(s(n)) == p(uminus(n))
    uminus_p: |- forall n. uminus(p(n)) == s(uminus(n))
    minus = (x,y) -> plus(x,uminus(y))

    times_p: |- forall x,n. times(x,s(n)) == minus(times(x,n), x)
  }
  class Rat {
    include Int
    frac: (num,num) -> num
    inv = x -> frac(o,x)

    int_embed: |- forall x. frac(x,o) == x
    frac_zero: |- forall x. frac(z,x) == z

    cancel: |- forall xe,xd,ye,yd. (frac(xe,xd) == frac(ye,yd)) == (times(xe,yd) == times(ye,xd))

    succ_frac:        |- forall e,d.   s(frac(e,d))       == frac(plus(e,d),d)
    pred_frac:        |- forall e,d.   p(frac(e,d))       == frac(minus(e,d),d)
    plus_frac_left:   |- forall e,d,x. plus(frac(e,d),x)  == frac(plus(e,times(d,x)),d)
    plus_frac_right:  |- forall e,d,x. plus(x,frac(e,d))  == frac(plus(times(x,d),e),d)
    uminus_frac:      |- forall e,d.   uminus(frac(e,d))  == frac(uminus(e),d)
    times_frac_left:  |- forall e,d,x. times(frac(e,d),x) == frac(times(e,x),d)
    times_frac_right: |- forall e,d,x. times(x,frac(e,d)) == frac(times(x,e),d)
    frac_frac_left:   |- forall e,d,x. frac(x,frac(e,d))  == frac(times(x,d),e)
    frac_frac_right:  |- forall e,d,x. frac(frac(e,d),x)  == frac(e,times(d,x))
  }
  class Complex {
    include Rat

    comp: (num,num) -> num

    rat_embed: |- forall r. comp(r,z) == r

    succ_comp:        |- forall r,i.   s(comp(r,i)) == comp(s(r),i)
    pred_comp:        |- forall r,i.   p(comp(r,i)) == comp(p(r),i)
    plus_comp_left:   |- forall r,i,x. plus(comp(r,i),x)  == comp(plus(r,x),i)
    plus_comp_right:  |- forall r,i,x. plus(x,comp(r,i))  == comp(plus(x,r),i)
    uminus_comp:      |- forall r,i.   uminus(comp(r,i))  == comp(uminus(r),uminus(i))
    times_comp_left:  |- forall r,i,x. times(comp(r,i),x) == comp(times(r,x),times(i,x))
    times_comp_right: |- forall r,i,x. times(x,comp(r,i)) == comp(times(x,r),times(x,i))
    frac_comp_left:   |- forall r,i,x. frac(x,comp(r,i))  == frac(times(x,comp(r,uminus(i))), minus(square(r),square(i)))
    frac_comp_right:  |- forall r,i,x. frac(comp(r,i),x)  == comp(frac(r,x),frac(i,x))
    comp_comp_left:   |- forall r,i,x. comp(comp(r,i),x)  == comp(r,plus(i,x))
    comp_comp_right:  |- forall r,i,x. comp(x,comp(r,i))  == comp(minus(x,i),r)

    conj: num -> num
    conj_comp: |- forall r,i. conj(comp(r,i)) == comp(r,uminus(i))
  }
}

module Algebra {
  class Carrier {
    type U
  }
  class Magma {
    include Carrier
    op: (U,U) -> U
  }
  class Semigroup {
    include Magma
    assoc: |- forall x,y,z. op(op(x,y),z) == op(x,op(y,z))
  }
  class Monoidal {
    include Magma
    e: U
  }
  intAdd = Magma {type U = int, op = (x,y) -> x+y}
  intMult = Magma {type U = int, op = (x,y) -> x*y}
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
      parent: Node?
    }
    makeNode = (l,p) -> Node {label = l, parent = p}

    class SearchStrategy {
       type Fringe
       init: [state] -> Fringe
       empty: Fringe -> bool
       insert: Fringe -> (Node,state) -> Fringe
       takeNext: Fringe -> (Fringe,Node)
    }

    DFS = SearchStrategy {
      type Fringe = [Node]
      init = ss -> ss match {
        [] -> []
        h-:t -> makeNode(h,[]) -: init(t)
      }
      empty = l -> l == []
      insert = l -> (p,s) -> makeNode(s, [p]) -: l
      takeNext = l -> l match {
        h -: t -> (t,h)
      }
    }

    treeSearch: (SearchProblem, SearchStrategy) -> Node? = (prob,strat) -> {
      var fringe: strat.Fringe = strat.init(prob.initials)
      while (!strat.empty(fringe)) {
         (fringe, val node) = strat.takeNext(fringe)
         if (prob.goals(node.label)) return [node]
         else
           for (a in prob.enumAllActions)
             for (s in prob.transitions(node.label, a))
               fringe = strat.insert(fringe)(node, s)
      }
      []
    }
}

main = {M.test}