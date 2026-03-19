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

        inconsistent = forall F. ⊦F 
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

    theory Booleans {
        include TypedTerms
        boolean : tp
    }
}