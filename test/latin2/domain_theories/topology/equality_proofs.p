module equality_proofs {
  theory ClosureSystem_Eq {
      include .definitions.ClosureSystem
  }

  theory Closeness_Eq {
      include .definitions.Closeness
  }

  theory ClosureOperator_Eq {
      include .definitions.ClosureOperator
  }

  theory DiagramCommutes {
      include .definitions.ClosureTopology
      include .definitions.ClosedTopology
  }

  theory ClosedTopology_Eq {
      include .definitions.ClosedTopology
  }

  theory ClosenessTopology_Eq {
      include .definitions.ClosenessTopology
  }

  theory ClosureTopology_Eq {
      include .definitions.ClosureTopology
  }

  theory InteriorTopology_Eq {
      include .definitions.InteriorTopology
  }

  theory NeighborhoodTopology_Eq {
      include .definitions.NeighborhoodTopology
  }

  theory OpenTopology_Eq {
      include .definitions.OpenTopology
  }
}
