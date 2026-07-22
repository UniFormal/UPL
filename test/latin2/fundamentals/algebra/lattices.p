module meta_lattices {
    theory MeetSemilattice {
        include .relations.Carrier
        meetOp: (univ,univ) -> univ # infix ⊓
        meet = .magmas.Semilattice {
            type univ = ..univ,
            op = meetOp,
            idem = idem,
            comm = comm,
            assoc = assoc
        }
    }

    theory JoinSemilattice {
        include .relations.Carrier
        joinOp: (univ,univ) -> univ # infix ⊔
        join = .magmas.Semilattice {
            type univ = ..univ,
            op = joinOp,
            idem = idem,
            comm = comm,
            assoc = assoc
        }
    }

    theory BoundedMeetSemilattice {
        include MeetSemilattice
        top: univ
        bmeet = .monoids.Monoid {
            type univ = ..univ,
            op = meet.op,
            e = top,
            inverse = inverse,
            inverse_sym = inverse_sym,
            inverse_unique = inverse_unique,
            inverse_neutral = inverse_neutral,
            inverse_op = inverse_op,
            involution_inverse = involution_inverse
        }
    }

    theory BoundedJoinSemilattice {
        include JoinSemilattice
        bottom: univ
        bmeet = .monoids.Monoid {
            type univ = ..univ,
            op = join.op,
            e = bottom,
            inverse = inverse,
            inverse_sym = inverse_sym,
            inverse_unique = inverse_unique,
            inverse_neutral = inverse_neutral,
            inverse_op = inverse_op,
            involution_inverse = involution_inverse
        }
    }

    theory LatticeAlgebra {
        include MeetSemilattice
        include JoinSemilattice
        absorb_meet_join:--- meet.op(x, join.op(x, y)) == x
        absorb_join_meet:--- join.op(x, meet.op(x, y)) == x
    }

    theory BoundedLatticeAlgebra {
        include LatticeAlgebra
        include BoundedMeetSemilattice
        include BoundedJoinSemilattice
    }
}