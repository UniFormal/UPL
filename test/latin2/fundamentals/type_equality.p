module type_equality {
    theory TypeEqualityND {
        include .concepts.Types
        include .concepts.Logic

        tpeq: .equality.UntypedEquality {
            type term = tp, 
            type prop = ..prop
        }

        relapply # infix ≛ = tpeq.uequal
    }

    theory DependentTypeEquality {
        include TypeEqualityND
        include .equality.TypedEqualityND

        congType: (A,x,y) -> ded tequal(A, x, y) -> B -> ded (B x ≛ B y)

        transport: (A,B) -> ded A≛B -> tm A -> tm B
        // ugly without implicit args
        transport_refl: ???
        transport_trans: ???
    }
}