// ////////
// Various minimal examples to reproduce errors
// ////////
module m{
  i = 0
  f: int -> int = x -> x+1
}

// ////////



// ////////

module Precedence{
  x: int
  test: |- x^2 + x^2 == 2
}

// ////////

// module DependentTypes{
//   theory Vectors {
//     concat@a: (m,n) // while checking m: open module not a type
//   }
// }

// ////////

module TypeWithParameter{
  theory Proofs {
    type prop
    // Judgement as types
    type ded(p: prop)
    lemma: F -> ded F
    // noLemma: ded F
    // unknownLocation: dud F -> text 
  }
}

// ////////

module DotWeirdness{
  const = 0
  theory T{
    works1 : |- 0 == const 
    works1 : |- .const == 0 // no declaration clash, and no hover for `const`
    fails1 : |- 0 == .const

    works2 : |- 0 == m.i // no hover for `m.i`
    fails2 : |- 0 == .m.i
    
    works3 : |- 0 + const == 0
    fails3 : |- 0 + .const == 0
  } 
}

// ////////

module DelayedClash{
  theory T1{
    i = 0
  }
  theory T2{
    i = 1
    include T1
  }
}

// ////////

module MutableKeywords{
  var = 0
  theory T{ 
    x = .var
    y = var 
    z = 2
    test = y == 2
  }
  t = T{}
  test = {
    ASSERT(t.x, 0)
    ASSERT(t.y, 0) // ??
    ASSERT(t.z, 2) // ??
    }
}

// ////////

module UnderscoreName{
  _ = 0
  _ = 1 // while checking val _ : int = 1: declaration clash

  _f: int -> int = x -> x 
  f: string -> int = _ -> 2
  foo = x -> {if (x<1) x else _f(1)} // `else _f(1)` is parsed as `else _ ; f(1)`

  test={
    _ = 0
    _ = 1
    ASSERT({if (true) 0 else _f(1)}, 1) 

    // Those crash the parser, currently
    // ASSERT({if (true) 0 else _f(1)}, _f(1))
    // ASSERT(_f(1), _f(1)) // Causes `name expected; found [Nothing]` loop
  }
  // x = ASSERT(_g, ) 
}
 
// //////// NullPointer when hovering `i`; also ..i != m.i, which might be intended

// module m { 
//   val i = 0 
//   theory T{ 
//     k = ..i
//   }
// }

// //////// r is "already defined differently"

module FailingMerge{
  theory T1 {
    i: int = 0815
    r: rat = 8/15
    f: float = 0.815
    s: string = "NullAchtFufzehn"
    b: bool = true
    calc: int = 8 + 15
    }
  theory T2 {
    include T1
    i: int = 0815
    r: rat = 8/15
    f: float = 0.815
    s: string = "NullAchtFufzehn"
    b: bool = true
    calc: int = 8 + 15
  }
}

// //////// `unexpected closing bracket`

// theory T1 {r:rat = 8/15}
// theory T2 {include T1 r:rat = 8/15}

// ////////

module gujizub{
  type point
  f:point -> float
  theory generic{
    A: point
    theory instance{
      A_P: |- f(A) == 90.0
    }
  }
  theory t {
    p: point 
    t: |- f(p) == 90.0
    test2:_ = generic{A = p}.instance{A_P}
  }
}

// ////////// 

// theory t{ a: int }
// p: t -> bool
// theory t2{
//   i: int
//   crash : |- p(t{a=i})
// } 

// ////////// Maximum call stack size exceeded

module CallStackExceeded{
  // include CallStack
  // include Exceeded

  // callStackExceeded: (a: _, b: _) -> (a:_, b:_, |- a==b)
  // callStackExceeded = (a, b) -> (a, b, ???)

  harmless: (a: _, b: _) -> (a:_, b:_, |- a==b) = (a, b) -> (a, b, ???)
}

// //////// Magic functions 

module MagicErrors{
  theory Magic{
    x: int
    val _infix_++ = (y: Magic) -> Magic{x=..x+y.x}
    val _infix_+   = (y: Magic) -> Magic{x=..x+y.x} // overload declaration is fine  
    val _circumfix_〈  = (as: list[Magic]) -> {Magic{x=1}}
    val _circumfix_〈$ = (as: list[Magic]) -> {Magic{x=1}}
    val _circumfix_$〈 = (as: list[Magic]) -> {Magic{x=1}}
  }
  a = Magic{x=1}
  b = Magic{x=2}
  works1 = a++b
  works2 = a++Magic{x=2}
  errors = {
    ASSERT(a++Magic{x=2}, works2) // while checking MagicErrors.Magic{val x : int = 2}: must be deterministic
    Magic{x=1} ++ b // magic function _infix_++ not found in {include T ...}
    Magic{x=1} ++ Magic{x=2} // same
    a+b // no matching type for operator
    ASSERT(a+b, works1)
    〈 a, b 〉 
    $〈 a,b 〉$ // while checking $〈a,b〉$: no constant with appropriate notation found in type: $
    〈$ a,b $〉 // while checking 〈$a,b$〉: no constant with appropriate notation found in type: 〈
  }
}

// ////////// `while checking z2: clashing definitions for p`: 3, and .z1{p} (== 3)

// theory ZmodP {
//   p: int
//   raw: int
//   modP:int -> int 
//   modP(z:int) = if (z<p & z>0) z else modP(z-p)
//   // magic infix operator: a ++ n becomes a._infix_++(n); here: add n to x
//   val _infix_++ = (y: ZmodP{p=..p}) -> ZmodP{p=..p, raw=modP(..raw+y.raw)}
// }
// z1 = ZmodP{p=3, raw=2}
// z2 = ZmodP{p=3, raw=2}
// test = ASSERT((z1++z2).raw, 1)

// //////////  while checking T{i} == 1: ill-typed equality: T{int}, int

// theory T { 
//   i: int = 1
// }
// test = ASSERT(T.i, 1)

// ////////// nested theories don't work in the slightest
module NestedTheories{
  theory outer{
    theory inner{
      x: int
      y:int = x
      fixed:int = 1
    }
    t1:_ = inner{x = 1}
    t2:_ = inner{x = 1, y = 1}
    t3:_ = inner{x = 1, y = x}
    t4: inner = t1
    t5: inner = t2
    t6: inner = t3
    test = {
      ASSERT(t1.x, t1.y)
      ASSERT(t1.x, t1.fixed)
      ASSERT(t2.x, t2.y)
      ASSERT(t2.x, t2.fixed)
      ASSERT(t3.x, t3.y)
      ASSERT(t3.x, t3.fixed)
      }
  }
}
// ////////// IndexOutOfBoundsException: 2

// x = ASSERT()

// //////////

// module NullPointerFactory{
//   include doesnt.exist
// }    

// //////////

// t: (int, int) = (1,2,3) // also throws `unexpected number of values`

// //////////

theory Point { 
  type univ 
  new: univ
  }
theory dummy { d: () }
point = Point{type univ = dummy, new = dummy{d = () } } // () is "not deterministic" ??

theory Situation{
  P: point
  Q: point
  E: |- P == Q 
}

// //////////

// a : (n:int, |- n==0)
// b : (n:int, |- n==0) 
// a = (b(1), b(2)) // throws `null` (not a NullPointer)
// a=b 
// c : (m:int, |- m==0)
// a=c // the types are alpha-equivalent 

// //////////

// module NotInPhysicalTheory{
//   theory t1 {
//     f = true
//     theory t2{
//       e: |- f = ??? // throws `not in physical theory`
//     }
//   }
// }

// //////////

theory A{
  a: (n:int, |- n==0)
}
theory B{
  realize A
  b: (m:int, |- m==0) = (0,???)
  a = (b(1), b(2)) // error: everything is fine ??
  //a = b
}

// //////////

// a : (n:int, |- n==0) 
// b : (m:int, |- m==0) = (0, ???)
// a = b
// c = (b(1), b(2))
// a = (a(1), a(2))
// b = b

// //////////

// theory Outer{
//   i: int
//   theory Inner{
//     j = i+1
//   } 
// }
// theory t{
//   include Outer{i=0}.Inner
// }

// theory Generic{
//   a: int  
//   b: int
//   r: (x:int, |- x == a+b) = (a+b, ???)
// }
// theory T{
//   A = 1 
//   B = 0
// } 
// theory Appl{
//   include T
//   type instance = Generic{a=A}
//   inst : instance
//   R1 = Generic{a=A, b=B}.r
//   R2 = inst{b=B}.r
// } 

// //////////

// h = doesn{t=???}.exist

// //////////

// val m = {1 match {
//   [] -> "hi" 
//   h
// }}
// val t = 1 match{n}

//test = doesnt.exist{P = 1}

// //////////

// theory HilbertSpace { 
//     type univ = Numbers.Complex{type num = (re: rat, im: rat)}
//     type num = (re: rat, im: rat) 
//     type hvector = (nat, nat) -> num
//     t: univ 
// }
