// module m{
//   type point
//   f:point -> float
//   theory _generic{
//     _A: point
//     theory _instance{
//       _t: |- f(_A) == 90.0
//     }
//   }
//   theory t {
//     p: point 
//     t: |- f(p) == 90.0
//     test2:_ = _generic{_A = p}._instance{_t}
//   }
// }

// //////////

// theory t{ a: int }
// p: t -> bool
// theory t2{
//   i: int
//   crash : |- p(t{a=i})
// } 

// //////////

// type fact = (a:_, b:_, |- a==b)
// fact1: (a: _, b: _) -> (a:_, b:_, |- a==b) 
// fact1 = (a, b) -> (a, b, ???)

// //////////

// theory B {
//   x: int 
//   val _circumfix_〈$_$〉 = (as: list[B]) -> {B{x=1}}
//   val _circumfix_〈!_〉 = (as: list[A]) -> {B{x=1}}
// }
// b=B{x=1}
// shouldErrorInDefinition = 〈!b,b〉.x
// shouldWork = 〈$b,b$〉.x
// unknown = 🗲〈a,a〉.Nothing

// //////////

// theory ZmodP {
//   p: int
//   raw: int
//   modP:int -> int 
//   modP(z:int) = if (z < p & z > 0) z else modP(z-p)
//   // magic infix operator: a ++ n becomes a._infix_++(n); here: add n to x
//   val _infix_++ = (y: ZmodP{p=..p}) -> ZmodP{p=..p, raw=modP(..raw+y.raw)}
// }
// z1 = ZmodP{p=3, raw=2}
// z2 = ZmodP{p=3, raw=2}
// test = (z1++z2).raw == 1

//////////

// theory t { 
//   f: int
// }
// i = t.f

//////////

// theory outer{
//   theory inner{
//     i: int
//     get = i
//   }
//   t1 = inner{i = 1}
//   v11 = t1.i
//   v1 = t1.get

//   t2 = inner{i = 1, get = 1}
//   v2 = t2.get

//   t3 = inner{i = 1, get = i}
//   v3 = t3.get
// }

//////////

// module does{
//     theory exist{}
// }
// module m{
//     theory t1{
//         include doesnt.exist
//     }
//     theory t2{ 
//         include does.exist
//     }
// } 

//////////

// theory n {}
// _ = n.u.ll

//////////

// t: (int, int) = (1,2,3)

//////////

// theory _point { 
//   type univ 
//   new: univ
//   }
// theory dummy { d: () }
// point = _point{type univ = dummy, new = dummy{d = () } }

// theory Situation{
//   P: point
//   Q: point
//   E: |- P == Q 
// }

//////////

// a : (n:int, |- n==0)
// b : (n:int, |- n==0)
// a=b
// c : (m:int, |- m==0)
// a=c

//////////

// f = (|- true ) -> 1

//////////

// theory t1 {
//     f = true
//     theory t2{
//         e: |- f = ??? 
//     }
// }

/////////

// theory A{
//   a: (n:int, |- n==0)
// }
// theory B{
//   realize A
//   b: (m:int, |- m==0) = (0,???)
//   a = (b(1),b(2))
//   a = b
// }

// a : (n:int, |- n==0) 
// b : (m:int, |- m==0) = (0, ???)
// a = b
// a = (b(1), b(2))
// a = (a(1), a(2))
// b = b

//////////

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

////////////

// h = doesn{t=???}.exist

///////////

// theory t{
//   include doesnt
//   include exist 
// } 

//////////

// val m = {1 match {
//   [] -> "hi" 
//   h
// }}
// val t = 1 match{n}

//test = doesnt.exist{P = 1}