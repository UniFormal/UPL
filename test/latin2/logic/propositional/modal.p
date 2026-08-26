module modal {
    theory Box {
        include .concepts.Propositions
        box: prop -> prop # prefix □
    }

    theory Diamond {
        include .concepts.Propositions
        diamond: prop -> prop # prefix ◇
    }

    theory ML {
        include .pl.PL
        include .concepts.Logic
        include Box
        include Diamond
    }

    theory MLHilbert {
        include ML
        // Rules with hypothetical premises are not sound in Kripke models; so we need to use a Hilbert calculus.
        include .pl_hilbert.PLHilbert
    }
}