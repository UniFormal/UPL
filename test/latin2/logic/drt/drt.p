module drt {
    // A formalization of Discourse Representation Theory (Hans Kamp \cite{Kamp:atotas81}; 
    // see also \cite{KamRey:acffodrs96}).
    // This formalization is patterned after https://kwarc.info/people/mkohlhase/papers/dlc00.pdf
    // only that we restrict ourselves to the first-order case. 
    // We give DRSes and Conditions a mode (in the type), where modes record the binding 
    // and bindable (i.e. free) discourse referents. 
    // In particular, the modes allow us to predict binding potentials; just see the positive 
    // referents in the mode. 
    // The modes have special computation rules here, so that they are normalized correctly.

    theory DRT {
        type dr //Discourse Referents
        type mode //DLC modes, they annotate the dynamic status of DRs
        pos: dr -> mode # postfix ⁺
        neg: dr -> mode # postfix ⁻
        empty: mode # nullfix ∅
        punion: (mode, mode) -> mode # infix ⊎

        type mequal(m1: mode, m2: mode)
        refl: (x) -> mequal(x, x)
        // bounded semi-lattice

        capture: (x) -> mequal(x⁺ ⊎ x⁻, x⁺) //specifying DR capture

        close: mode -> mode # postfix ↓
        close_pos: (x) -> mequal((x⁺)↓, ∅)
        close_neg: (x) -> mequal((x⁻)↓, x⁻)
        close_empty: mequal((∅)↓, ∅)
        close_close: (x) -> mequal((x↓)↓, x↓)

        // don't know how to do this
        // normal form of modes: set of DRs with function into boolean
        // rule ☞scala://modes.drt.latin2?NormalizePunion

        type drs(m: mode)
        type tm(m: mode)
        type cond(m: mode)

        // DRSs
        atomic: (m,n) -> cond n -> drs (m ⊎ n) // m is just set of drs, all mapped with pos in the return type
        merge: (m,n) -> drs m -> drs n -> drs (m ⊎ n)
        seqmerge: (m,n) -> drs m -> drs n -> drs (m ⊎ n↓)

        // conditions
        and: (m,n) -> cond m -> cond n -> cond (m ⊎ n)
        dneg: (m) -> drs m -> cond m
        dimpl: (m,n) -> drs m -> drs n -> cond ((m ⊎ n↓)↓)

        // terms
        idref: (i) -> tm (i⁻)
    }

    Example : DRT {
        // example for a predicate
        farmer: (m) -> tm m -> cond m
        donkey: (m) -> tm m -> cond m
        stick: (m) -> tm m -> cond m
        beat: (l,m,n) -> tm l -> tm m -> cond n -> cond ((l ⊎ m) ⊎ n)
        own: (m,n) -> tm m -> tm n -> cond (m ⊎ n)
        u: dr
        v: dr
        w: dr
        uv: mode = u⁺ ⊎ v⁺
        // A farmer owns a donkey
        fod = ???
        // He beats it with a stick
        fbds = ???
        // the iconic DRT example: If a farmer owns a donkey, he beats it with a stick
        donkey_sentence = ???
    }
}