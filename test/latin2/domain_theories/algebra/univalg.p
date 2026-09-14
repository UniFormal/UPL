module univalg {
    // Experimental deep embedding of algebra theories, to eventually formalize theorems of universal algebra.
    //
    // Author: Navid Roux
    // Date: started 2021-11-08
    //
    // The work is based on:
    //
    // [DeM21] William DeMeo. "The Agda Universal Algebra Library and Birkhoff's Theorem in Dependent Type Theory".
    //         In: CoRR abs/2101.10166 (2021). source code: https://gitlab.com/ualib/ualib.gitlab.io.
    //         url: https://arxiv.org/abs/2101.10166.
    //
    // See also Navid's review of that in their M.Sc. thesis (when it's ready) in the chapter
    // "Operators for Universal Algebra".

    theory Meta {
    }

    theory Base {
    }

    // Test theory for jcombd, jcombc used for bracket notation
    theory TestTest {
    }

    theory Homomorphisms {
        include Base
    }
}
