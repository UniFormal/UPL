module equivalences {
  // views between the isomorphic axiomatizations of closure systems/operators:
  //
  // ClosureOperator -> ClosureSystem: cl A = intersection of closed supersets of A
  // ClosureSystem -> Closeness: A closed if A contains all points close to it
  // Closeness -> ClosureOperator: x is close to A if x in cl A

//   ClosureOperatorToClosureSystem: .definitions.ClosureSystem -> .definitions.ClosureOperator = c -> §{
//       include .definitions.BaseSet
//   }

//   ClosureSystemToCloseness: .definitions.Closeness -> .definitions.ClosureSystem = c -> §{
//       include .definitions.BaseSet
//   }

//   ClosenessToClosureOperator: .definitions.ClosureOperator -> .definitions.Closeness = c -> §{
//       include .definitions.BaseSet
//   }

  // views between the isomorphic axiomatizations of topologies
  //
  // ClosedTopology -> ClosenessTopology: A closed if A contains all points close to it
  // ClosenessTopology -> ClosureTopology: x is close to A if x in cl A
  // ClosureTopology -> InteriorTopology: cl A = complement of the interior of the complement of A
  // InteriorTopology -> NeighborhoodTopology: interior A = the set of all x close to A
  // NeighborhoodTopology -> OpenTopology: N is a neighborhood of x if there is an open subset O of A with x in O
  // OpenTopology -> ClosedTopology: A is open if its complement is closed

//   ClosedTopologyToClosenessTopology: .definitions.ClosenessTopology -> .definitions.ClosedTopology = c -> §{
//       include ClosureSystemToCloseness
//   }

//   ClosenessTopologyToClosureTopology: .definitions.ClosureTopology -> .definitions.ClosenessTopology = c -> §{
//       include ClosenessToClosureOperator
//   }

//   ClosureTopologyToInteriorTopology: .definitions.InteriorTopology -> .definitions.ClosureTopology = c -> §{
//       include .definitions.BaseSet
//   }

//   InteriorTopologyToNeighborhoodTopology: .definitions.NeighborhoodTopology -> .definitions.InteriorTopology = i -> §{
//       include .definitions.BaseSet
//   }

//   NeighborhoodTopologyToOpenTopology: .definitions.OpenTopology -> .definitions.NeighborhoodTopology = n -> §{
//       include .definitions.BaseSet
//   }

//   OpenTopologyToClosedTopology: .definitions.ClosedTopology -> .definitions.OpenTopology = o -> §{
//       include .definitions.BaseSet
//   }
}
