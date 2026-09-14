module power_types {
  // We modify symbols with jcombx, because there is no jcombp.

  // TODO: eventually show that this realizes EndoLattice (which itself should be generated using Polymorphify)

  theory PowerTypes {
      include .equality.TypedEqualityND
      include .pl.EquivalenceND
  }

  theory Map {
      include PowerTypes
      include .pl.ConjunctionND
      include .sfol.TypedExistentialQuantificationND
  }

  theory Preimage {
      include PowerTypes
  }

  theory Extensionality {
      include PowerTypes
      include .sfol.TypedUniversalQuantificationND
  }

  theory FiniteSets {
      include PowerTypes
      include .pl.DisjunctionND
  }

  theory Subset {
      include PowerTypes
      include Extensionality
      include .pl.ImplicationND
  }

  theory FullSet {
      include PowerTypes
      include .pl.TruthND
  }

  theory EmptySet {
      include PowerTypes
      include .pl.FalsityND
  }

  theory Complement {
      include PowerTypes
      include .pl.NegationND
  }

  theory Intersection {
      include PowerTypes
      include .pl.ConjunctionND
  }

  theory Union {
      include PowerTypes
      include .pl.DisjunctionND
  }

  theory BigIntersection {
      include PowerTypes
      include .pl.ImplicationND
      include .sfol.TypedUniversalQuantificationND
  }

  theory BigUnion {
      include PowerTypes
      include .pl.ConjunctionND
      include .sfol.TypedExistentialQuantificationND
  }

  theory Lattice {
      include Map
      include Preimage
      include Extensionality
      include Subset
      include FullSet
      include EmptySet
      include Complement
      include Intersection
      include Union
      include BigIntersection
      include BigUnion
  }

  theory SubsetRules {
      include Lattice
  }

  theory ComplementRules {
      include Lattice
      include SubsetRules
      include .pl.PLND
  }

  theory EmptyRules {
      include SubsetRules
  }

  theory FullRules {
      include SubsetRules
  }

  theory PowerSFOL {
      include .sfol.SFOLEQND
      include PowerTypes
      include FiniteSets
      include Lattice
      include SubsetRules
      include ComplementRules
      include EmptyRules
      include FullRules
  }
}
