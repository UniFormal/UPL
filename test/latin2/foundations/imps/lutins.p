module lutins {
    // The underlying logic for IMPS is called LUTINS (Logic of Undefined
    // Terms for Inference in a Natural Style). This Higher-Order-Logic
    // incorporates partial functions, undefinedness and subtyping.
    //
    // More details can be found at http://imps.mcmaster.ca/manual/node12.html

    theory Lutins {
    }

    theory LutinsUndefinedness {
        include Lutins
        // include NonDenotingND // TODO: not in LATIN
        // include UndefinedND // TODO: not in LATIN
    }

    theory LutinsProofs {
        include Lutins
    }

    theory QuasiLutins {
        include LutinsProofs
    }
}
