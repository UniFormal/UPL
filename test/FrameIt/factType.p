module factType_experiments{
  theory Type { type univ }
  point = Type { type univ = int }
  theory Fact{ 
    type univ
    type dependencies = list[Fact]
    value: univ
    dep: dependencies
  }
  theory FuncFact{
    include Fact
    func: dependencies -> univ
    core: |- func(dep) == value
  }
  
  dist: point -> point -> float
  theory Dist{
    type univ = float
    P: point
    Q: point
    d: univ
    dist_proof: |- dist(P)(Q) == d = ???
  }
}