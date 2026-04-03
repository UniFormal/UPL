module equality {
    theory UntypedEquality {
        include .base_languages.UntypedLogic

        uequal: (term, term) -> prop    # infix ≐
    }

    theory UntypedEqualityND {
        include UntypedEquality

        urefl:--- ⊦(X ≐ X)
        ucongP:--- ⊦(X ≐ Y) => ⊦P(X) => ⊦P(Y)
    }

    theory SoftTypedEquality {
        include .base_languages.SoftTypedLogic

        requal: (tp, term, term) -> prop
    }

    theory SoftTypedEqualityND {
        include SoftTypedEquality

        rrefl:--- ⊦ requal(A, X, X)
        requal_tp:--- ⊦ requal(A, X, X) => ⊦ of(X, A) 
        rsym:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, X)
        rtrans:--- ⊦ requal(A, X, Y) => ⊦ requal(A, Y, Z) => ⊦ requal(A, X, Z)
        requal_any_tp:--- ⊦ requal(A, X, Y) => ⊦ of(X, A)
    }
}