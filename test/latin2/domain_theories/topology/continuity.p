module continuity {
  theory TopologyMap {
  }

  theory ReflectsClosedness {
      include TopologyMap
  }

  theory ReflectsOpenness {
      include TopologyMap
  }

  theory ReflectsNeighborhood {
      include TopologyMap
  }

  theory PreimageExpandsInterior {
      include TopologyMap
  }

  theory ExpandsClosure {
      include TopologyMap
  }

  theory PreservesCloseness {
      include TopologyMap
  }

  ReflectsOpennessToReflectsClosedness: ReflectsClosedness -> ReflectsOpenness = r -> §{
      include TopologyMap
  }

  // proof fails because some of the morphisms in topology.mmt had to be commented out
  ReflectsClosednessToPreservesCloseness: PreservesCloseness -> ReflectsClosedness = r -> §{
      include TopologyMap
  }

  PreservesClosenessToExpandsClosure: ExpandsClosure -> PreservesCloseness = p -> §{
      include TopologyMap
  }

  ExpandsClosureToPreimageExpandsInterior: PreimageExpandsInterior -> ExpandsClosure = e -> §{
      include TopologyMap
  }

  PreimageExpandsInteriorToReflectsNeighborhood: ReflectsNeighborhood -> PreimageExpandsInterior = p -> §{
      include TopologyMap
  }

  ReflectsNeighborhoodToReflectsOpenness: ReflectsOpenness -> ReflectsNeighborhood = r -> §{
      include TopologyMap
  }

  theory Continuous {
      include TopologyMap
  }
}
