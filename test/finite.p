module FiniteStructures {
  theory FiniteCarrier {
    size: int
    type univ = int[0;size]
  }
  theory Graph {
    include FiniteCarrier
    type node = univ
    edgeTo: univ -> Set[univ]
  }
  reflexive = (g: Graph) -> forall x: g.node. x in g.edgeTo(x)
  loop = Graph {size = 1, edgeTo = x -> [x]}
  test = reflexive(loop)
}
