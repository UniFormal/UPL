module loops {
  theory WhileOps {
      include .equality.TypedEquality
      include .pl.Classical
      include .mutability.MutableVariables
  }

  theory ForLoop {
      include WhileOps
      include .nat.Nat
  }
}
