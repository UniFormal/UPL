module definitions {
  theory BaseSet {
      include .sets.Set
  }

  // isomorphic axiomatizations of closure systems/operators
  theory ClosureSystem {
      include BaseSet
  }

  theory ClosureOperator {
      include BaseSet
  }

  theory Closeness {
      include BaseSet
  }

  // isomorphic axiomatizations of topologies
  theory InteriorTopology {
      include BaseSet
  }

  theory ClosureTopology {
      include ClosureOperator
  }

  theory ClosenessTopology {
      include Closeness
  }

  theory OpenTopology {
      include BaseSet
  }

  // axioms/theorems are dual to OpenTopology
  theory ClosedTopology {
      include ClosureSystem
  }

  theory NeighborhoodTopology {
      include BaseSet
  }
}
