module fol_tableaux {
	theory UniversalQuantificationTab {
        include .fol.UniversalQuantification
        include .pl_tableaux.Tableaux
        forallT: (P,X) -> marktrue(∀ᵘ P) -> (marktrue(P X) -> closedbranch) -> closedbranch
        forallF: (P) -> markfalse(∀ᵘ P) -> ((x) -> markfalse(P x) -> closedbranch) -> closedbranch
    }

    theory ExistentialQuantificationTab {
        include .fol.ExistentialQuantification
        include .pl_tableaux.Tableaux
        existsT: (P) -> marktrue(∃ᵘ P) -> ((x) -> marktrue(P x) -> closedbranch) -> closedbranch
        existsF: (P,X) -> markfalse(∃ᵘ P) -> (markfalse(P X) -> closedbranch) -> closedbranch
    }
}