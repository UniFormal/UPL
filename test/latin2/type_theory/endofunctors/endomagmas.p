module endomagmas {
  theory EndoMagma {
      include .endofunctors.EndoFunctor
  }

  theory EndoSemigroup {
      include EndoMagma
  }

  theory EndoCommutative {
      include EndoMagma
  }

  theory EndoNeutral {
      include EndoMagma
  }

  theory EndoIdempotent {
      include EndoMagma
  }

  theory EndoFirstNonNeutral {
      include EndoNeutral
  }

  theory EndoMonoid {
      include EndoSemigroup
      include EndoNeutral
  }

  theory EndoCommSemigroup {
      include EndoSemigroup
      include EndoCommutative
  }

  theory EndoBand {
      include EndoSemigroup
      include EndoIdempotent
  }

  theory EndoCommMonoid {
      include EndoMonoid
      include EndoCommSemigroup
  }

  theory EndoSemilattice {
      include EndoBand
      include EndoCommSemigroup
  }

  theory EndoBoundedSemilattice {
      include EndoSemilattice
      include EndoCommMonoid
  }
}
