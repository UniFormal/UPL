module topology {
  theory Closure {
      include .definitions.ClosureSystem
      include .definitions.ClosureOperator
      include .definitions.Closeness
  }

  theory Topology {
      include Closure
      include .definitions.ClosedTopology
      include .definitions.OpenTopology
      include .definitions.NeighborhoodTopology
      include .definitions.InteriorTopology
      // These declarations are semantically correct, but MMT cannot certify that because of a non-trivial equality between morphisms.
      // We have the following diagram, where C and T abbreviate Closure and Topology, and i-edges are inclusions from inside to outside.
      // The subdiagrams marked // commute by construction, and MMT can exploit that.
      // The subdiagram marked //? also commutes, but MMT does not know that.
      // The equality is non-trivial because it requires equality reasoning in the object logic (as well as proof irrelevance).
      //
      //      OpenT --------------> ClosedT
      //         ^                  /i     \
      //        /              CSystem      \
      //       /      //?       ^  \    //   \
      //      /                 |   v         v
      // NeighborhoodT          |  Closeness-i-CloseT
      //      ^                 |   /         /
      //       \                |  v    //   /
      //        \              COperator    /
      //         \                    \i   v
      //    InteriorT <-------------- ClosureT

      // include ?ClosureTopology = ?ClosureTopologyToInteriorTopology
      // include ?ClosenessTopology = ?ClosenessTopologyToClosureTopology
  }
}
