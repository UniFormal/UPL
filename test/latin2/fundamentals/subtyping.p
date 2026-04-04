module subtyping {
    theory Subtyping {
        include .concepts.Types
        include .concepts.Logic

        subtype: (tp, tp) -> prop # infix ⪽
    }

    theory SoftSubtyping {
        include .concepts.SoftTypedTerms
        include Subtyping

        // subtypeI:--- 
    }
}