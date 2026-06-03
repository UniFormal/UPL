module lattices {
    theory MeetSemilattice {
        include .magmas.Semilattice
        meet: (univ,univ) -> univ # infix ⊓
        op = meet
    }

    theory JoinSemilattice {
        include .magmas.Semilattice
        join: (univ,univ) -> univ # infix ⊔
        //op = join
    }

    theory BoundedMeetSemilattice {
        include MeetSemilattice
        include .monoids.Monoid
        top: univ
        e = top
    }

    theory BoundedJoinSemilattice {
        include JoinSemilattice
        include .monoids.Monoid
        bottom: univ
        //e = bottom
    }

    theory LatticeAlgebra {
        include MeetSemilattice
        include JoinSemilattice
        absorb_meet_join:--- (x⊓(x⊔y)) == x
        absorb_join_meet:--- (x⊔(x⊓y)) == x
    }

    theory BoundedLatticeAlgebra {
        include LatticeAlgebra
        include BoundedMeetSemilattice
        include BoundedJoinSemilattice
    }
}