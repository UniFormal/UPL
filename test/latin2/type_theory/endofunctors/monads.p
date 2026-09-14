module monads {
  theory Applicative {
      include .endofunctors.TypeOperator
  }

  theory Monad {
      include .endofunctors.TypeOperator
  }

  theory InternalMonad {
      include .endofunctors.TypeOperator
  }

  KleisliCat: InternalMonad -> .category.Category = k -> §{
  }
}
