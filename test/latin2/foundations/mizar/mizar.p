module mizar {
    theory Mizar {
        include .stfol.SoftTypedDefinedFOL
    }

    theory HIDDEN {
        include Mizar
    }
}
