module collection_types {
  theory Collection {
      include .endomagmas.EndoMagma
      include .endomagmas.EndoNeutral
      include .nat.Nat
  }

  theory NonIdempotentCollection {
      include Collection
  }

  theory CommutativeCollection {
      include Collection
  }

  theory BinaryTreeSpec {
      include Collection
  }

  theory ListSpec {
      include NonIdempotentCollection
      include .endomagmas.EndoMonoid
  }

  theory MultisetSpec {
      include ListSpec
      include .endomagmas.EndoCommutative
  }

  theory FiniteSetSpec {
      include MultisetSpec
      include .endomagmas.EndoIdempotent
  }

  theory OptionSpec {
      include ListSpec
      include .endomagmas.EndoFirstNonNeutral
  }

  theory ResultSpec {
      include Collection
      include .endomagmas.EndoMonoid
  }

  theory Lists {
      include .nat.Nat
  }

  theory Multisets {
      include .nat.Nat
  }

  theory FiniteSets {
      include .nat.Nat
  }

  theory BinaryTrees {
  }

  theory Options {
  }
}
