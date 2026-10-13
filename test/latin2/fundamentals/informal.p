module informal {
    theory InformalProofs {
        include .concepts.Proofs
        
        proofsketch: A -> string -> ded A
        trivial: A -> ded A = A -> proofsketch A "trivial"
    }
}