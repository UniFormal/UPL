module linear {
    // This was copied here from MMT/examples. It still needs to be adjusted and should not be built yet.
    // The same applies to the corresponding Scala rules, which are currently commented out.

    // Linear logic
    //
    // Syntax: intuitionistic linear logic
    //
    // Proof theory: resource semantics based on Frank Pfenning's lecture notes
    // (http://www.cs.cmu.edu/~fp/courses/15816-s10/schedule.html, Lecture 23-24) resource semantics

    theory Syntax {

    }

    // We use untyped first-order logic with equality to define the semantics.
    // The values of the first-order universe are the worlds, and propositions may hold at different worlds.

    theory Worlds {
        include Syntax
    }

    // Apart from the monoid/multiset structure, there is no way to introduce worlds.
    // The set of worlds is the freely-generated T over the bound world variables.
    // Here T is the theory imposed on worlds, T is an extension of the monoid theory.
    // Different extensions allow modeling different structural rules.
    // The following gives three extensions, but only Exchange is used later on.

    // Exchange corresponds to commutativity.
    theory Exchange {
        include Worlds
    }

    // Contraction corresponds to idempotence.
    theory Contraction {
        include Worlds
    }

    // Weakening corresponds to the empty world being the least element.
    theory Weakening {
        include Worlds
    }

    // Now proofs of the linear sequent A1, ..., An |- A are represented as terms of type
    // (A1 ⊗ ... ⊗ An) ⊸ A  @  ε, where @ is the binary holds-at relation between propositions and worlds.

    theory ResourceSemantics {
        include Worlds
        include Exchange
    }
}
