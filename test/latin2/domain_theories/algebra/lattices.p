module lattices {
    theory MeetSemilattice {
        include .sets.Set
    }

    theory JoinSemilattice {
        include .sets.Set
    }

    theory BoundedMeetSemilattice {
        include MeetSemilattice
    }

    theory BoundedJoinSemilattice {
        include JoinSemilattice
    }

    theory LatticeAlgebra {
        include MeetSemilattice
        include JoinSemilattice
    }

    theory BoundedLatticeAlgegra {
        include LatticeAlgebra
        include BoundedMeetSemilattice
        include BoundedJoinSemilattice
    }
}
