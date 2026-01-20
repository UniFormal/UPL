// Modules and theories are the grouping elements. They are named and can be nested.
// They roughly correspond to Java packages resp. classes or Isabelle theories resp. locales.
// Modules are just namespaces: Moving a declaration between modules just means different qualified names must be used to reference declarations.
// File and folder names are irrelevant for qualified names - only the module names matter.

module P1 {
  module P2 {
    c: int
  }
}

module P2 {
  // access a declaration from a different module by its qualified name
  // an optional leading . ensures that a qualified name is absolute
  d = .P1.P2.c
}

// Theories provide encapsulation, abstraction, inheritance, and world-closure:
// - New instances of a theory can be created (by defining all undefined fields) and used (by accessing a field) in OO style.
// - The terms in the language induced by the declarations of a theory can be constructed and pattern-matched in the style of inductive types.

// For more on theories, see the respective files.
// The remainder of this file explains the basics of types and expressions.

module Basic {
  // Atomic declaration in a module/theory can be for types and terms (values).
  type a = int
  val c1: a = 0
  // The keyword "val" may be omitted. Types are inferred if omitted.
  c2 = 0
  
  // Dependent product types, tuples, and positional access are written with (...).
  t: (x:int,s:string) = (1,"foo")
  t_1: int = t(1)

  // Dependent function types and lambda abstractions are written with (...) -> ..., application as fun(args).
  f1 : int -> int = (x:int) -> x+1
  // Inferable parts can be omitted.
  f2 = (x:int) -> x+1
  f3 : int -> int = x -> x+1
  // _ can be used to omit an inferrable type explicitly.
  f4 : int -> _ = x -> x+1
  // Functions may be curried or take multiple arguments as once:
  f5_multiarg: (int,int) -> int = (x,y) -> x+y
  f5_multiarg_applied = f5_multiarg(0,1)
  f5_curried:   int -> int -> int = x -> y -> x+y
  f5_curried_applied = f5_curried(0)(1)
  // Arguments may also be declared right after the function name
  // They  apply to type and definiens, i.e., the type is Pi-bound and the definiens lambda-bound.
  f5_multiarg_variant(x: int,y:int): int = x+y

  // Unused variable names (e.g., in product or function types) can be omitted.
  // _ can be used to explicitly make a variable anonymous or to omit a type.
  // These are all the same as t above:
  t2: (x:int,string) = (1,"foo")
  t3: (_:int,string) = (1,"foo")
  t4: (_,    string) = (1,"foo")
  t5: (_,    _)      = (1,"foo")
  t6: _              = (1,"foo")

  // Multiple variables in a row can be given the same type using multiple colons:
  mutivar(v:bool, w,x,y:::int, z:bool) = w+x+y // Three colons => w,x and y have type int.
  mutivar2(v,x,y::int) = mutivar(v,x,x,x,v) // Two colons => x and y have type int; the type of v is inferred separately.
  // That also works if the types are omitted:
  mutivar3(v,x,y::_) = mutivar(v,x,y,x,v) // Types of x and y are the same; type of v is inferred separately.
  // mutivar4(v,x,y:::_) = mutivar(v,x,y,x,v) // Types of v,x and y are the same; doesn't work.

  // Type inference works across the whole module/theory.
  // Here the input type of 'id' is inferred from its use, and its return type from its body.
  id = x -> x
  id0 = id(0)

  // Terms may also be {}-blocks. These are sequences of terms that evaluate to their last element.
  factorial = (x:int) -> {
    // return statements return from the current named function (even if the return type has not been infered yet).
    if (x<0) return 1
    // var/val introduce immutable/mutable variables that are visible for the remainder of the block.
    // Types can be inferred, initialization is mandatory.
    var result = 1
    var i = 1
    // if and while can be used as usual.
    while (i<=x) {
      result = result*i
      i = i+1
    }
    // no "return" needed for the last expression
    result
  }

  // Repeated declarations for the same name are merged.
  // That can be used to give type and definition separately.
  // That is necessary for recursive functions to make sure the name already exists when the definiens is processed:
  factorial2: int -> int
  factorial2 = x -> {
    if (x <= 0) return 1
    x * factorial2(x-1)
  }

  // The two declarations do not have to occur right after one another. That is used for mutual recursion.
  odd: int -> _  // inferrable types can be omitted even with recursive functions
  even = x -> (x == 0) | if (x>0) odd(x-1) else odd(-x-1)
  odd = x -> if (x == 0) false else even(x-1)

  // string, int, rat, float, bool are the usual base types.
  // int is a subtype of rat. Both are unbounded.
  // rat is converted to float with precision loss if typing requires it.
  
  // empty and any are the least and greatest element of the subtype lattice.
  // () is the unit type and unit value (indistinguishable from empty tuple).
  v1: any
  v2: empty -> () = _ -> ()

  // The built-in operators for the built-in types are usual ones. They are ad-hoc polymorphic where appropriate.

  // Arithmetic operators:

  int_add(x,y:: int): int = x+y
  rat_add(x,y:: rat): rat = x+y
  float_add(x,y::float):float = x+y
  // Type inference guesses that all arguments have the same type. Mixed-type arguments are converted as needed.
  float_add2(x:float, y) = x+y // (float,float)->float
  int_float_add(x: int, y: float) = x+y // (int,float)->float

  // Accordingly for -, *, /, <=, >=, <, >.

  // Division by 0 throws a run-time exception.
  int_div(x,y:: int) = x/y // (int,int) -> rat

  // Equality == and inequality != are polymorphic and can be used for every type.
  // Evaluation is attempted but may fail if equality is undecidable.
  returns_true = ((x:int) -> x) == ((x:int) -> x) // reflexivity of == always succeeds
  would_fail = () -> ((x:int) -> x+1) == ((x:int) -> x)

  // Interval types can be formed as subtypes of int.
  // This makes type-checking undecidable, but the checker tries its best and fails if it cannot verify the type.
  c3: int[0;2] = c1
  c4: (x:int, y:int[0;x]) = (1,0)
  // The intervals can be unbounded on either side.
  type nat = int[0;]

  // variables may be named or unnamed

  // Boolean operators:
  conj(x,y:: bool): bool = x & y
  impl(x,y:: bool): bool = x => y
  disj(x,y:: bool): bool = x | y
  neg(x: bool): bool = !x
  
  // All binary operators short-circuit.
  // Theorem provers may assume the truth (resp. falsity) of x when processing x&y or x=>y (resp. x|y).
  no_exception = false & (1/0 == 1)

  // Collection types are written using []:
  // - C[T] for the type
  // - C[x1,...,xn] for elements
  // - l[p] for positional access (if possible)
  // Here "C" can be set, list, bag, option. If omitted, it defaults to 'list'.
  ls: list[int] = [1,2,3,4]
  ls0 = ls[0] // Index bounds are not checked and may cause run-time errors.
  // -: and :- are cons and snoc.
  ls2 = 1 -: 2 -: [3] :- 4

  // Collections form a subtype hierarchy using both inclusion and quotient.
  // In particular, options and lists are special cases of sets:
  quotient_list_to_set:  set[int] = list[1,1,2]
  include_option_to_set: set[int] = option[0]

  // for (x in L) {...} iterates over collections.
  foreach : ([int], int -> ()) -> () = (l,f) -> {for (i in l) f(i); ()}
  map = (l: [int]) -> f -> {
    var r: [int] = []
    for (x in l) {r = r :- f(x)}
    r
  }
  // pattern-matching is written 'l match {pattern -> body, ...}'
  map2:_
  map2 = (l: [int]) -> (f: int -> int) -> {
    l match {
      [] -> []
      hd -: tl -> f(hd) -: map2(tl)(f)
    }
  }

  // Closures are taken when lambda-abstractions refer to mutable variables declared outside of the lambda.
  sum = l -> {
    var x = 0
    val f = (y:int) -> {
      x = x+y; ()
    }
    foreach(l,f)
    x
  }

  // exn is the type of exceptions, throw/catch use the same syntax as return/match except for the change in keyword

  // Exeptions are declared by creating functions that return exn.
  // This is one of the cases where definition-less declarations in a module make sense.
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
  // conjunction and implication short-circuit
  dynamicAnd = false & {throw error("not run")}
  dynamicImply = false => {throw error("not run")}

  // Some operators allow dynamic binding: names bound in one argument A of P may be visible in another argument B of P.
  // Dynamic binding only happens for certain combinations of P, A, and B.
  // In such a case, a Boolean A may also be a pattern-matching declaration - then A evaluates to 'true' if it matches.
  dynamicNames = (x:list[int], expected) -> {
    // Dynamic binding happens if P is if-then-else: A is the condition, and B is the then-branch.
    // Here, if x is of the form [u,v], u and v are visible in the then-branch
    val k = if ([val u, val v] = x) u+v else 0
    // Dynamic binding also happens if P is a short-circuiting connective: A and B are the left and right argument.
    // (But if A is an implication, it does not export any bindings, i.e., (true => (val x=1)) & x==1 is illegal.)
    val q = ([val u, val v] = x) & (val z = u+v) => z == k
    k == expected & q
  }
  dynamicBinding = deepBinding1 & !dynamicAnd & dynamicImply & dynamicNames([1,2], 3) & dynamicNames([1], 0)

  testNewline = {
    val x = 1
    val f = (u:int) -> u+1
    // postfix operations like (), [], ., etc. must be at the end of the line
    // parsed as function application
    val fx = f(
      x
    )
    // parsed as two expression the second of which happens to be bracketed
    val y = x
    (x+y)*2
  }

  // some tests for the above
  test = {
    sum([1,2,3]) == 6 &
    factorial(3) == 6 &
    map([1,2,3])(x -> x+1) == [2,3,4] &
    map2([1,2,3])(x -> x+1) == [2,3,4] &
    divide(5,0) == 0 &
    dynamicBinding &
    ac == ("a","c")
  }
}