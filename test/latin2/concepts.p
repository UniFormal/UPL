module concepts {
    theory Propositions {
        type prop
    }

    theory Proofs {
        include Propositions
        ded : prop -> bool  # prefix ⊦
        
        lemma:--- ⊦F => (⊦F => ⊦G) => ⊦G
    }

    theory Disproofs {
        include Propositions
        disproof : prop -> bool
    }

    theory Logic {
        include Propositions
        include Proofs

        inconsistent : bool = forall F. ⊦F 
        inconsistentE:--- inconsistent => ⊦F

        realize Disproofs
        disproof = F -> (⊦F => inconsistent)
    }

    theory Terms {
        type term
    }

    theory Types {
        type tp
    }

    theory TypedTerms {
        include Types
        tm : tp -> bool
    }

    theory SoftTypedTerms {
        include Terms
        include Types
        include Propositions

        of : term -> tp -> prop
    }

    theory Kinds {
        type kd
    }

    theory KindedTypes {
        include Kinds
        include Types

        tpk : kd

        hasKind : tp -> kd -> bool
        isType = A -> hasKind(A)(tpk)

        arrow : kd -> kd -> kd

        app : tp -> tp -> tp
        app_kind:--- hasKind(F)(arrow(A)(B)) => hasKind(X)(A) => hasKind(app(F)(X))(B)
    }

    theory KindedTypesTest {
        include KindedTypes

        Nat : tp
        Nat_type : |- isType(Nat)
        Nat_kind : |- hasKind(Nat)(tpk)

        List : tp
        list_type : |- isType(List) // this should fail
        list_kind : |- hasKind(List)(arrow(tpk)(tpk))

        // l : app(List)(Nat) // doesn't work, why?
        l = app(List)(Nat)
        l_type : |- isType(l)

        Pair : tp
        pair_kind : |- hasKind(Pair)(arrow(tpk)(arrow(tpk)(tpk)))
    }

    theory Booleans {
        include TypedTerms
        boolean : tp
    }

    // theory InternalPropositions {
    //     include Booleans
    //     realize Propositions
    //     prop = tm(boolean)
    // }

}