module universes {
    theory SoftUniverses {
        include .base_languages.TypedLogic
        level: (tp, tp) -> prop # infix ⋳
    }

    theory TwoUniverses {
        include SoftUniverses
        utp: tp
        ukd: tp
        utp_kd:--- ⊦(utp ⋳ ukd)
    }

    theory UniverseHierarchy {
        include SoftUniverses
        type univ
        univ_zero: univ
        univ_next: univ -> univ

        univTp: univ -> tp
        univ_in:--- ⊦(univTp U ⋳ univTp (univ_next U))

        realize TwoUniverses
        utp = univTp univ_zero
        ukd = univTp (univ_next univ_zero)
        utp_kd = ???
    }

    theory InclusiveUniverses {
        include UniverseHierarchy
        inclusive:--- ⊦(A ⋳ univTp U) => ⊦(A ⋳ univTp (univ_next U))
    }

    theory UniverseDepFunExample {
        include SoftUniverses
        type Pi_legal(a: tp, b: tp)
        Pi: A -> (tm A -> tp) -> tp

        // is this correct?
        Pi_legal_check: tp -> tp -> prop
        Pi_univ:--- forall B: tm A -> tp. ⊦(A ⋳ U) => (forall x: tm A. ⊦((B x) ⋳ U)) => ⊦(Pi_legal_check U V) => ⊦((Pi A B) ⋳ V)

        include TwoUniverses
        function_types: Pi_legal(utp, utp)
        dependent_types: Pi_legal(utp, ukd)
    }
}