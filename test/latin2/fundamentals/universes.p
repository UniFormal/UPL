module universes {
    // Universes as a soft typing relation (level) on types
    // tp is now no longer the base universe -- instead, it is the union of all universes
    // We define a universe to be any type that occurs on the left of the level relation.
    theory SoftUniverses {
        include .base_languages.TypedLogic
        level: (tp, tp) -> prop # infix ⋳
        univTm: (A, U) -> ded A⋳U
    }

    // single universes of types and kinds
    theory TwoUniverses {
        include SoftUniverses
        utp: tp
        ukd: tp
        utp_kd: ded utp⋳ukd
    }

    // natural number-based hierarchy of universes
    theory UniverseHierarchy {
        include SoftUniverses
        type univ
        univ_zero: univ
        univ_next: univ -> univ

        univTp: univ -> tp
        univ_in: U -> ded (univTp U ⋳ univTp (univ_next U))

        realize TwoUniverses
        utp = univTp univ_zero
        ukd = univTp (univ_next univ_zero)
        // doesn't work
        utp_kd = ??? // univ_in
    }

    // Universes as a soft element typing relation on types
    theory InclusiveUniverses {
        include UniverseHierarchy
        inclusive: (A, U) -> ded (A ⋳ univTp U) -> ded (A ⋳ univTp (univ_next U))
    }

    theory UniverseDepFunExample {
        include SoftUniverses
        type Pi_legal(a: tp, b: tp)
        Pi: A -> (tm A -> tp) -> tp
        Pi_univ: (U,V,A,B) -> (x -> ded (B x ⋳ V)) -> Pi_legal(U, V) -> ded (Pi A B ⋳ V)
        // lambda, apply, etc. as usual

        // LF as a λ-cube example
        include TwoUniverses
        function_types: Pi_legal(utp, utp)
        dependent_types: Pi_legal(utp, ukd)
    }
}