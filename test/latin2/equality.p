module equality {
    theory UntypedEquality {
        include .base_languages.UntypedLogic

        uequal: (term, term) -> prop    # infix ≐
    }

    theory UntypedEqualityND {
        include UntypedEquality

        urefl:--- ⊦ X ≐ X
        ucongP:--- ⊦ X ≐ Y => ⊦P(X) => ⊦P(Y)
    }

    theory SoftTypedEquality {
        include .base_languages.SoftTypedLogic

        requal: (tp, term, term) -> prop
        as: (⊦ of(X, A)) -> term // this probably doesn't work right?
    }

    theory SoftTypedEqualityND {
        include SoftTypedEquality

        rrefl:--- ⊦ requal(A, X, X)
        requal_tp:--- ⊦ requal(A, X, X) => ⊦ of(X, A) 
        rsym:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, X)
        rtrans:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, Z) => ⊦ requal(A, X, Z)
        requal_any_tp:--- ⊦ requal(A, X, Y) => ⊦ of(X, A)
        // requal_as // I don't know
        // rcongP // I don't know
    }

    theory TypedEquality {
        include .base_languages.TypedLogic

        tequal: tm(A) -> tm(A) -> prop // this probably doesn't work right?
    }

    theory TypedEqualityND {
        include TypedEquality

        trefl:--- ⊦ tequal(X, X)
        tcongB:--- (forall a. ⊦ tequal(X(a), Y(a))) => forall P. ⊦P(X) => ⊦P(Y)
        tcongP:--- ⊦ tequal(X, Y) => forall P. ⊦P(X) => ⊦P(Y)
        tsym:--- ⊦ tequal(X, Y) => ⊦ tequal(Y, X)
        ttrans:--- ⊦ tequal(X, Y) => ⊦ tequal(Y, Z) => ⊦ tequal(X, Z)
        // more missing 
    }

    theory PropositionalExtensionality {
        //include .concepts.InternalPropositions // missing
        include TypedEquality

        propext:--- (⊦F => ⊦G) => (⊦G => ⊦F) => ⊦(tequal(F, G))
        top_unique:---  ⊦F => ⊦G => ⊦(tequal(F, G))
    }
}