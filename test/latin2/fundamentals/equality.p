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
            type univ = term
            rel = (x,y) -> ⊦uequal(x,y)
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
        // as: dedT(of(x, A)) -> term
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
        tequal: (A, tm A , tm A) -> prop
    }

    theory TypedEqualityND {
        include TypedEquality
        trefl:--- forall x:tm A. ⊦ tequal(A, x, x)
        tcongB:--- forall X, Y: tm A -> tm B. (forall a: tm A. ⊦ tequal(B, X a, Y a)) => forall P: (tm A -> tm B) -> prop. ⊦(P X) => ⊦(P Y)
        tcongP:--- forall x, y: tm A. ⊦ tequal(A, x, y) => forall P: tm A -> prop. ⊦(P x) => ⊦(P y)
        tcongT:--- forall x, y: tm A. ⊦ tequal(A, x, y) => forall T: (tm A -> tm B). ⊦ tequal(B, T x, T y)
        tsym:--- forall x, y: tm A. ⊦ tequal(A, x, y) => ⊦ tequal(A, y, x)
        ttrans:--- forall x, y, z: tm A. ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, x, z)
        ttrans3:--- forall w, x, y, z: tm A. ⊦ tequal(A, w, x) => ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, w, z)
        ttrans4:--- forall v, w, x, y, z: tm A. ⊦ tequal(A, v, w) => ⊦ tequal(A, w, x) => ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, v, z)
        tcongT2:--- forall x1, y1: tm A, x2, y2: tm B. ⊦ tequal(A, x1, y1) => ⊦ tequal(B, x2, y2) => forall T: (tm A -> tm B -> tm C). ⊦ tequal(C, T x1 x2, T y1 y2)

        eqChain:--- forall x:tm A. ⊦ tequal(A, x, x)
        equalToVia:--- forall T, X: tm A. ⊦ tequal(A, T, X) => forall Y: tm A. ⊦ tequal(A, X, Y) => ⊦ tequal(A, T, Y)
    }

    theory PropositionalExtensionality {
        include .concepts.InternalPropositions
        include TypedEquality
        propext:--- (⊦ F => ⊦ G) => (⊦ G => ⊦ F) => ⊦ tequal(boolean, F, G)
        top_unique:--- ⊦ F => ⊦ G => ⊦ tequal(boolean, F, G)
    }
}