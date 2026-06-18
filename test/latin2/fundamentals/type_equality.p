module type_equality {
    theory TypeEqualityND {
        include .concepts.Types
        include .concepts.Logic

        tpeq: .equality.UntypedEquality {type term = tp, type prop = ..prop}
    }

    theory DependentTypeEquality {
        include TypeEqualityND
        include .equality.TypedEqualityND

        congType:--- forall x,y: tm A. ⊦ tequal(A, x, y) => forall B: (tm A -> tp). ⊦tpeq.uequal(B x, B y)

        // don't know how to do this
        transport: ???
        transport_refl: ???
        transport_trans: ???
    }
}