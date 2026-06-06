module equality {
    theory UntypedEquality {
        include .base_languages.UntypedLogic
        uequal: (term, term) -> prop    # infix ≐
    }

    theory UntypedEqualityND {
        include UntypedEquality
        urefl:--- ⊦(X ≐ X)
        ucongP:--- ⊦(X ≐ Y) => ⊦P(X) => ⊦P(Y)

        eq: .relations.EquivalenceCongruence {
            // needs type-valued decrarations
            // univ = term
            // rel = (x,y) -> uequal(x,y)
            refl = ???
            sym = ???
            trans = ???
            congT = ???
        }
    }

    theory SoftTypedEquality {
        include .base_languages.SoftTypedLogic
        requal: (tp, term, term) -> prop

        // don't know how to do this
        as: ???
    }

    theory SoftTypedEqualityND {
        include SoftTypedEquality

        rrefl:--- ⊦ requal(A, X, X)
        requal_tp:--- ⊦ requal(A, X, X) => ⊦ of(X, A) 
        rsym:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, X)
        rtrans:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, Z) => ⊦ requal(A, X, Z)
        requal_any_tp:--- ⊦ requal(A, X, Y) => ⊦ of(X, A)
        
        // don't know how to do this
        requal_as: ???
        rcongP: ???
    }

    theory TypedEquality {
        include .base_languages.TypedLogic
        tequal: A -> tm A -> tm A -> prop
    }
}