// Modules and theories are the grouping elements. They are named and can be nested.
// They roughly correspond to Java packages resp. classes or Isabelle theories resp. locales.
// Modules are just namespaces: Moving a declaration between modules just means qualified names have to change.
// Theories provide encapsulation, abstraction, inheritance, and world-closure:
// - New instances of a theory can be created (by defining all undefined fields) and used (by accessing a field) in OO style.
// - The terms in the language induced by the declarations of a theory can be constructed and pattern-matched in the style of inductive types.
module M {
  // Atomic declaration in a module/theory can be for types and terms. The latter uses no keyword.
  // string, int, bool are the usual base types.
  type a = int
  c1: a = 0
  // Types are inferred if omitted.
  c2 = 0
  
  // Interval types can be formed as subtypes of int.
  // This makes type-checking undecidable, but the checker tries its best and fails if it cannot verify the type.
  c3: int[0;2] = c1
  // The intervals can be unbounded on either side.
  type nat = int[0;]
  
  // Tuples types, tuples, and positional access are written with (...).
  t: (int,string) = (1,"foo")
  t1: int = t(1)

  // Collections are written using []: C[T] for the type, [x1,...,xn] for elements, and l[p] for positional access.
  // The collection kind "C" can be set, list, bag, option. If omitted, it defaults to 'List'.
  ls: list[int] = [1,2,3,4]
  ls0 = ls[0] // Index bounds are not checked and may cause run-time errors.
  // Collections for a subtype hierarchy, i.e., lists are special cases of sets.
  st: set[int] = ls
  // -: and :- are cons and snoc.
  ls2 = 1 -: 2 -: [3] :- 4

  // Function types and lambda abstractions are written with (...) -> ...
  f1 : int -> int = (x:int) -> x+1
  // Inferable parts can be omitted.
  f2 = (x:int) -> x+1
  f3 : int -> int = x -> x+1
  // _ can be used to omit a type explicitly that should be inferred.
  f4 : int -> _ = x -> x+1

  // Terms may also be {}-blocks. These are sequences of terms that evaluate to their last element.
  factorial = (x:int) -> {
    // return statements return from the current named block (even if the return type has not been infered yet.)
    if (x<0) return 1
    // var/val introduce mutable/immutable variables that are visible for the remainder of the block.
    // Types can be inferred, initialization is mandatory.
    var result = 1
    var i = 1
    // if and while can be used as usual.
    while (i<=x) {
      result = result*i
      i = i+1
    }
    result
  }

  // Repeated declarations of the same name are merged, e.g., to refine the type or to supply a definition.
  // Combined with _ for an omitted type, that can be used to obtain recursion.
  factorial2: _
  factorial2 = (x:int) -> {
    if (x <= 0) return 1
    x * factorial2(x-1)
  }

  // Type inference works across the whole module/theory.
  // Here the input type of 'id' is inferred from its use, and its return type from its body.
  id = x -> x
  id0 = id(0)

  // This style of forward references also enables mutual recursion.
  odd: _
  even = x -> x == 0 | if (x>0) odd(x-1) else odd(-x-1)
  odd = x -> if (x == 0) false else even(x-1)

  // theories work like classes or record types
  theory Person {
    // In a theory, declarations may undefined, i.e., abstract.
    name: string
    age: int
    male: bool
    // Definitions are terms, e.g., if-else is an inline operator.
    address = (if (male) "Mr" else "Mrs") + " " + name
  }

  theory Man {
    // Theories may be included into other modules/theories.
    include Person
    // Definitions are type-checked against the inherited type.
    male = true
  }

  // Theories are abstract if any field is undefined, otherwise concrete.
  // Concrete theories can be instantiated by defining the remaining abstract fields.
  // No 'new' keyword is used.
  me = Man {name = "Florian", age = 45}

  // () is the unit type. for (x in L) {...} iterates over collections.
  foreach : ([int], int -> ()) -> () = (l,f) -> {for (i in l) f(i); ()}
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = f(x) -: r}
    r
  }
  // pattern-matching is written 'l match {pattern -> body, ...}'
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      hd-:tl -> f(hd)-:map2(tl)(f)
    }
  }

  // exn is the type of exceptions, throw/catch use the same syntax as return/match except for the change in keyword
  error: string -> exn
  divide = (x:int,y:int) -> {
    if (y==0) throw error("second argument must be non-zero")
    x/y
  } catch {
    error(_) -> 0
  }

  // Variable declarations and assignments may use a pattern on the LHS
  ac = {
    val abc = ["a", "b", "c"];
    // split 'abc' into "a" -: ["b","c"] and assign a = "a"
    (val a) -: _ = abc;
    // c = "c" accordingly
    _ :- (val c) = abc;
    (a,c)
  }

  // Variable declarations can occur inside other expressions, in which case they evaluate to their initial value.
  deepBinding1 = {factorial(factorial(val n = 3)); n+1} == 4

  // Closures are taken when lambda-abstractions refer to mutable variables declared outside of the lambda.
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }

  // some tests for the above
  test = {
    M.sum([1,2,3]) == 6 &
    M.factorial(3) == 6 &
    M.map2([1,2,3])(x -> x+1) == [2,3,4] &
    divide(5,0) == 0 &
    deepBinding1 &
    ac == ("a","c")
  }
}