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

  theory Proofs {
    type prop
    // Judgement as types
    type ded(p: prop)
    lemma: (F, G) -> ded F -> (ded F -> ded G) -> ded G
  }
}