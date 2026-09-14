module generated {
  theory GeneratedSets {
      include .sets.Set
  }

  theory GeneratedMagmas {
      include .magmas.Magma
      include GeneratedSets
  }

  theory GeneratedPointed {
      include .magmas.Pointed
      include GeneratedMagmas
  }

  theory GeneratedInverseFun {
      include .groups.InverseFun
      include GeneratedPointed
  }
}