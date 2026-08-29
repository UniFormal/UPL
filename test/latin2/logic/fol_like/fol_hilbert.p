module fol_hilbert {
	theory UniversalQuantificationHilbert {
        include .fol.UniversalQuantificationNDE
        include .pl_hilbert.ImplicationHilbert
        UQ_ax: (P) -> ded(∀ᵘ ((x) -> P x) ⇒ ∀ᵘ P)
    }

    // The following views need to be built
    // HilbertNDEquivalence: .pl.EquivalenceNDI -> .pl_hilbert.EquivalenceHilbert = e -> .pl_hilbert.EquivalenceHilbert {
    //     UQ_ax =
    // }

    // NDHilbertEquivalence: .pl_hilbert.EquivalenceHilbert -> .pl.EquivalenceNDI = e -> .pl.EquivalenceNDI {

    // }
}