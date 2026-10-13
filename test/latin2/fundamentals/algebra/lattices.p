module meta_lattices {
    theory MeetSemilattice {
        include .relations.EqualityType
        meetOp: (carrier,carrier) -> carrier # infix ⊓
        meet = .magmas.Semilattice {
            type carrier = ..carrier,
            op = meetOp,
            idem = idem,
            comm = comm,
            assoc = assoc
        }
    }

    theory JoinSemilattice {
        include .relations.EqualityType
        joinOp: (carrier,carrier) -> carrier # infix ⊔
        join = .magmas.Semilattice {
            type carrier = ..carrier,
            op = joinOp,
            idem = idem,
            comm = comm,
            assoc = assoc
        }
    }

    theory BoundedMeetSemilattice {
        include MeetSemilattice
        top: carrier
        bmeet = .monoids.Monoid {
            type carrier = ..carrier,
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
        bottom: carrier
        bmeet = .monoids.Monoid {
            type carrier = ..carrier,
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