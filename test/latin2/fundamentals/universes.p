module universes {
    // Universes as a soft typing relation (level) on types
    // tp is now no longer the base universe -- instead, it is the union of all universes
    // We define a universe to be any type that occurs on the left of the level relation.
    theory SoftUniverses {
        include .base_languages.TypedLogic
        level: (tp, tp) -> prop # infix ⋳
        univTm: ???
    }

    // single universes of types and kinds
    theory TwoUniverses {
        include SoftUniverses
        utp: tp
        ukd: tp
        utp_kd:--- ⊦utp⋳ukd
    }

    // natural number-based hierarchy of universes
    theory UniverseHierarchy {
        include SoftUniverses
        type univ
        univ_zero: univ
        univ_next: univ -> univ

        univTp: univ -> tp
        univ_in:--- ⊦(univTp U)⋳(univTp (univ_next U))

        realize TwoUniverses
        utp = univTp univ_zero
        ukd = univTp (univ_next univ_zero)
        utp_kd = ???    // utp_kd = univ_in
    }

    // Universes as a soft element typing relation on types
    theory InclusiveUniverses {
        include UniverseHierarchy
        inclusive:--- ⊦A⋳(univTp U) => ⊦A⋳(univTp (univ_next U))
    }

    theory UniverseDepFunExample {
        include SoftUniverses
        Pi: A -> (tm A -> tp) -> tp

        Pi_legal: tp -> tp -> prop
        type Pi_legalT(a: tp, b: tp)

        Pi_univ:--- forall B: tm A -> tp. ⊦A⋳U => (forall x:tm A. ⊦(B x)⋳U) => ⊦(Pi_legal U V) => ⊦(Pi A B)⋳V
        // lambda, apply, etc. as usual

        // LF as a λ-cube example
        include TwoUniverses
        function_types: Pi_legalT(utp, utp)
        dependent_types: Pi_legalT(utp, ukd)
    }
}