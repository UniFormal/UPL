module factType_experiments{
  theory FactT{ 
    type univ
    type dependencies = list[FactT]
    value: univ
    dep: dependencies
  }
  theory FuncFact{
    include FactT
    func: dependencies -> univ
    core: |- func(dep) == value
  }

  theory Proofs {
    type prop
    // Judgement as types
    type ded(p: prop)
    lemma: (F, G) -> ded F -> (ded F -> ded G) -> ded G
  }

  theory PointsOpaque{
    type univ
  }
  Point = PointsOpaque{ type univ = int, p1: univ = 1 }

  //type Point
  type Distance(p: Point, q:Point) = float
  p1: Point = 1
  p2: Point
  test: Distance(p1,p2) = 2

  type Fact@(A,B)(A->B, A, B)
  observed@(A,B): (f:A->B) -> (a:A) -> (b:B) -> (|- f(a)==b) -> Fact@(A,B)(f,a,b)
  plusOne = x -> x+1
  trivial1: |- plusOne(1)==2
  test1:_ = observed plusOne 1 2 trivial1
  
  plus = (x:int,y) -> x+y
  plus2 = (x:int) -> y -> x+y
  trivial2: |- plus(1,1)==2
  //test2:_ = observed plus (1,1) 2 trivial2 // wrong number of components: 1, expected 2
}
