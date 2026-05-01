// Modules and theories are the grouping elements. They are named and can be nested.
// They roughly correspond to Java packages resp. classes or Isabelle theories resp. locales.
// Modules are just namespaces: Moving a declaration between modules just means different qualified names must be used to reference declarations.

// Theories have the same syntax as modules.
// But they provide encapsulation, abstraction, inheritance, and world-closure (see below).

module m1 {
  module m2 {
    c: int
  }
}

module m2 {
  // access a declaration from a different module by its qualified name
  // an optional leading . ensures that a qualified name is absolute
  module m1 {
    c: int
  }
  d = .m1.m2.c
  e = m1.c     // expands to .m2.m1.c
}

module IFIPBasics {
  // Atomic declaration in a module/theory can be for types and terms (values).
  type a = int
  c1: a = 0
  // Types are inferred if omitted.
  c2 = 0
  
  // Product types, tuples, and positional access:
  t: (x:int, s:string) = (1,"foo")
  t_1: int = t(1)

  // Function types and lambda abstractions are written with (...) -> ....
  f1: int -> int   = (x:int) -> x+1
  f2               = (x:int) -> x+1  // type omitted
  f3: int -> int   = x -> x+1        // type of bound variable omitted
  f4: int -> _     = x -> x+1        // return type omitted
  f5(x:int): int   = x+1             // alternative notation for argument bindings

  // type inference has theory scope
  f6: _
  // later in the same theory
  q: int = f6(1)  // type of f6 inferred

  // terms may be {}-blocks
  factorial = (x:int) -> {
    if (x<0) return 1 // contributes to inference of return type
    // val/var introduce immutable/mutable variables
    // types can be inferred, initialization is mandatory
    var result = 1
    var i = 1
    while (i<=x) {
      result = result*i
      i = i+1
    }
    result
  }

  // type and definition may be given separately
  f7: _ -> int
  f7 = (x:int) -> x+1

  // practical for recursion
  factorial2: int -> int
  factorial2 = x -> {
    if (x<=0) 1 else x * factorial2(x-1)
  }

  // or mutual recursion
  odd: int -> _
  even = x -> if (x == 0) true else odd(x-1)
  odd  = x -> if (x == 0) false else even(x-1)

  // string, int, rat, float, bool, empty, unit, any and built-in operators as usual
  // int is a subtype of rat, both are unbounded
  // rat is subtype of float (converted with precision loss)
  
  // collections are written with []
  // collections form a subtype hierarchy using both inclusion and quotient
  // lists are a subtype of sets
  quotient_list_to_set:  set[int] = list[1,1,2]

  // -: is cons, :- is snoc
  map:_
  map = (l: [int]) -> (f: int -> int) -> {
    l match {
      []         -> []
      hd -: tl   -> f(hd) -: map(tl)(f)
    }
  }

  // closures are taken when lambda-abstractions refer to mutable variables declared outside of the lambda.
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; 0
    }
    map(l)(f)
    x
  }

  // exn is the type of exceptions, throw/catch are treated internally almost like return/match
  error: string -> exn
  divide = (x:int,y:int) -> {
    if (y==0) throw error("second argument must be non-zero")
    x/y
  } catch {
    error(_) -> 0
  }

  // some tests for the above
  test = {
    ASSERT(sum([1,2,3]), 6)
    ASSERT(factorial(3), 6)
    ASSERT(map([1,2,3])(x -> x+1), [2,3,4])
    ASSERT(divide(5,0), 0)
  }

  theory h1 {
    a: int
    f: int -> int
  }

  // instances must define all fields (which subsumes proving all axioms)
  i1: h1 = h1 {a = 1, f = x -> x}  // h1 {d1,...} abbreviates {include h1, d1, ...}

  theory h2 {
    include h1     // expands into a:int, f:int->int
    f = x -> x+1   // merges with existing f into  f: int->int = x->x+1
  }
  theory h3 {
    realize h2     // like "include h2" but *all* fields must be defined
    a = 1          // fails without this line
  }

  theory h4 {
    include h1
    c: int
  }
  theory h5 {
    include h1 = i1  // defined includes yield delegation: all declarations from h1 are defined as in i1
  } // expands to {a=1, f=x->x, c: int}
}