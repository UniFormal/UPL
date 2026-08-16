module pl_semilattice {
    theory DisjunctionSL {
        include .pl.Lindenbaum
        include .pl.DisjunctionND
        realize .meta_magmas.Semilattice
        type term = prop
        type carrier = prop
        op = or
        idempotent = ???
        comm = ???
        assoc = ???
    }

    theory ConjunctionSL {
        include .pl.Lindenbaum
        include .pl.ConjunctionND
        realize .meta_magmas.Semilattice
        type term = prop
        type carrier = prop
        op = and
        idempotent = ???
        comm = ???
        assoc = ???
    }
}