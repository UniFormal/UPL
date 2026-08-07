module informal {
    theory InformalProofs {
        include .concepts.Proofs
        //this is a test
        proofsketch: A -> string -> ded A
        trivial: A -> ded A = A -> proofsketch A "trivial"
    }
}