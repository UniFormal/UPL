module sets {
    include .sfol.SFOLEQND

    theory Set {
        universe: tp
        type U = tm universe
    }

    theory SetHom {
        domain: Set
        codomain: Set
        U: domain.U -> codomain.U
    }

    theory SubSet {
        parent: Set
        U: parent.U -> prop
    }
}