module equality {
    theory UntypedEquality {
        include .base_languages.UntypedLogic
        uequal: (term, term) -> prop # infix ≐
    }

    theory UntypedEqualityND {
        include UntypedEquality
        urefl:--- ⊦x≐x
        ucongP:--- ⊦x≐y => forall P:term -> prop. ⊦(P x) => ⊦(P y)

        eq: .relations.EquivalenceCongruence {
            type carrier = term
            // has to be uequal, ≐ doesn't work
            rel = (x,y) -> ⊦uequal(x, y)
            refl = ???
            sym = ???
            trans = ???
            congT = ???
        }

        ucongPr:--- ⊦x≐y => forall P:term -> prop. ⊦(P y) => ⊦(P x)
    }

    // A relative equality for a typed language, in which the equality of objects may depend on the type at which it is taken.
    // This can be practical in connection with
    // - record types: two records are equal if they agree in all fields required by the type
    // - quotient types: equivalent representatives are equal if seen as elements of the quotient
    // - forgetful functors and other implicit conversions: two different groups may be equal as sets
    theory SoftTypedEquality {
        include .base_languages.SoftTypedLogic
        requal: (tp, term, term) -> prop
        as: (x, A, dedT x∶A) -> term
    }

    theory SoftTypedEqualityND {
        include SoftTypedEquality
        rrefl:--- ⊦ requal(A, x, x)
        requal_tp:--- ⊦ requal(A, x, x) => ⊦x∶A 
        rsym:--- ⊦ requal(A, x, Y) => ⊦ requal(A, Y, x)
        rtrans:--- ⊦ requal(A, x, Y) => ⊦ requal(A, Y, Z) => ⊦ requal(A, x, Z)
        requal_any_tp:--- ⊦ requal(A, x, Y) => ⊦x∶A
        
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

        // We use an unusual congruence in order to be able to perform congruence under an arbitrary binder.
        // The rule captures a |- X a = Y a ---> P [a] X a ⇔ P [a] Y a.
        // That suffices to derive the xi rule for λ later. 
        tcongB:--- forall X, Y::tm A -> tm B. (forall a: tm A. ⊦ tequal(B, X a, Y a)) => forall P: (tm A -> tm B) -> prop. ⊦(P X) => ⊦(P Y)
        
        //The usual congruence rule arises as a special case.
        tcongP:--- forall x, y::tm A. ⊦ tequal(A, x, y) => forall P: tm A -> prop. ⊦(P x) => ⊦(P y)
        tcongT:--- forall x, y::tm A. ⊦ tequal(A, x, y) => forall T: (tm A -> tm B). ⊦ tequal(B, T x, T y)
        tsym:--- forall x, y::tm A. ⊦ tequal(A, x, y) => ⊦ tequal(A, y, x)
        ttrans:--- forall x, y, z::tm A. ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, x, z)
        ttrans3:--- forall w, x, y, z::tm A. ⊦ tequal(A, w, x) => ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, w, z)
        ttrans4:--- forall v, w, x, y, z::tm A. ⊦ tequal(A, v, w) => ⊦ tequal(A, w, x) => ⊦ tequal(A, x, y) => ⊦ tequal(A, y, z) => ⊦ tequal(A, v, z)
        tcongT2:--- forall x1, y1::tm A, x2, y2::tm B. ⊦ tequal(A, x1, y1) => ⊦ tequal(B, x2, y2) => forall T: (tm A -> tm B -> tm C). ⊦ tequal(C, T x1 x2, T y1 y2)

        eqChain:--- forall x:tm A. ⊦ tequal(A, x, x)
        equalToVia:--- forall T, x::tm A. ⊦ tequal(A, T, x) => forall Y:tm A. ⊦ tequal(A, x, Y) => ⊦ tequal(A, T, Y)
    }

    theory PropositionalExtensionality {
        include .concepts.InternalPropositions
        include TypedEquality
        propext:--- (⊦ F => ⊦ G) => (⊦ G => ⊦ F) => ⊦ tequal(boolean, F, G)
        top_unique:--- ⊦ F => ⊦ G => ⊦ tequal(boolean, F, G)
    }
}