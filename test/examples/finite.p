module FiniteStructures {
  theory FiniteCarrier {
    size: int
    type univ = int[0;size]
  }
  theory Graph {
    include FiniteCarrier
    type node = univ
    edgeTo: univ -> set[univ]
  }
  reflexive = (g: Graph) -> forall x: g.node. x in g.edgeTo(x)
  loops = s -> Graph {size = s, edgeTo = x -> [x]}
  test = reflexive(loops(2))
}
