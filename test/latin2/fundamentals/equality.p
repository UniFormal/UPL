module equality {
    theory UntypedEquality {
        include .base_languages.UntypedLogic
        uequal: (term, term) -> prop # infix ≐
    }

    theory UntypedEqualityND {
        include UntypedEquality

        urefl: x -> ded x≐x
        ucongP: (x,y) -> ded x≐y -> P -> ded (P x) -> ded (P y)

        eq: .relations.EquivalenceCongruence {
            type carrier = term
            // doesn't work
            // type rel(c1:carrier, c2:carrier) = ded uequal(c1, c2)
            refl = ???
            sym = ???
            trans = ???
            congT = ???
        }

        ucongPr: (x,y) -> ded x≐y -> P -> ded (P y) -> ded (P x)
    }

    // A relative equality for a typed language, in which the equality of objects may depend on the type at which it is taken.
    // This can be practical in connection with
    // - record types: two records are equal if they agree in all fields required by the type
    // - quotient types: equivalent representatives are equal if seen as elements of the quotient
    // - forgetful functors and other implicit conversions: two different groups may be equal as sets
    theory SoftTypedEquality {
        include .base_languages.SoftTypedLogic
        requal: (tp, term, term) -> prop
        as: (x, A, ded x∶A) -> term
    }

    theory SoftTypedEqualityND {
        include SoftTypedEquality
        rrefl: (A,x) -> ded requal(A, x, x)
        requal_tp: (A,x) -> ded requal(A, x, x) -> ded x∶A 
        rsym: (A,x,y) -> ded requal(A, x, y) -> ded requal(A, y, x)
        rtrans: (A,x,y,z) -> ded requal(A, x, y) -> ded requal(A, y, z) -> ded requal(A, x, z)
        requal_any_tp: (A,x,y) -> ded requal(A, x, y) -> ded x∶A = ???
        
        requal_as: (A, x, y) -> ded requal(A, x, y) -> term = ???
        rcongP: (A, x, y, p, P) -> ??? // ugly without implicit args
    }

    theory TypedEquality {
        include .base_languages.TypedLogic
        tequal: (A, tm A , tm A) -> prop
    }

    theory TypedEqualityND {
        include TypedEquality
        trefl: (A,x) -> ded tequal(A, x, x)

        // We use an unusual congruence in order to be able to perform congruence under an arbitrary binder.
        // The rule captures a |- X a = y a ---> P [a] X a ⇔ P [a] y a.
        // That suffices to derive the xi rule for λ later. 
        tcongB: (A,B,X,Y) -> (a -> ded tequal(B, X a, Y a)) -> P -> ded (P X) -> ded (P Y)
        
        //The usual congruence rule arises as a special case.
        tcongP: (A,x,y) -> ded tequal(A, x, y) -> P -> ded (P x) -> ded (P y)
        tcongT: (A,B,x,y) -> ded tequal(A, x, y) -> T -> ded tequal(B, T x, T y)
        tsym: (A,x,y) -> ded tequal(A, x, y) -> ded tequal(A, y, x)
        ttrans: (A,x,y,z) -> ded tequal(A, x, y) -> ded tequal(A, y, z) -> ded tequal(A, x, z)
        ttrans3: (A,x,y,z,w) -> ded tequal(A, w, x) -> ded tequal(A, x, y) -> ded tequal(A, y, z) -> ded tequal(A, w, z)
        ttrans4: (A,x,y,z,w,v) -> ded tequal(A, v, w) -> ded tequal(A, w, x) -> ded tequal(A, x, y) -> ded tequal(A, y, z) -> ded tequal(A, v, z)
        tcongT2: (A,B,C,x1,y1,x2,y2) -> ded tequal(A, x1, y1) -> ded tequal(B, x2, y2) -> T -> ded tequal(C, T x1 x2, T y1 y2)

        eqChain: (A,X) -> ded tequal(A, X, X)
        equalToVia: (A,T,X) -> ded tequal(A, T, X) -> Y -> ded tequal(A, X, Y) -> ded tequal(A, T, Y)
    }

    theory PropositionalExtensionality {
        include .concepts.InternalPropositions
        include TypedEquality
        propext: (F,G) -> (ded F -> ded G) -> (ded G -> ded F) -> ded tequal(boolean, F, G)
        top_unique: (F,G) -> ded F -> ded G -> ded tequal(boolean, F, G)
    }
}