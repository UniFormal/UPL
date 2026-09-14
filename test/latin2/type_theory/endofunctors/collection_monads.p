module collection_monads {
  CollectionMonad: .collection_types.Collection -> .monads.Monad = c -> §{
  }

  theory FailMonad {
      include .strings.String
      include .coproduct_types.Coproducts
  }
}
