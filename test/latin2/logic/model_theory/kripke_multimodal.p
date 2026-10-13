module kripke_multimodal {
    // MMLSemantics: .kripke.Worlds -> .multimodal.MML = w -> §{
    //     include .concepts.Logic = .kripke.LogicSemantics(w)

    //     // note: `kripke.world` does not resolve; world is a field of Worlds, so it has to
    //     // come through the parameter as w{world}
    //     type modality = w{tm world} -> w{tm world} -> prop
    //     box = m -> p -> v -> tforall w{world} (v2 -> impl (m v v2, p v2))
    //     diamond = m -> p -> v -> texists w{world} (v2 -> and (m v v2, p v2))
    // }

    // SMMLSemantics: kripke.Worlds -> .multimodal.SMML = w -> §{
    //     include .multimodal.MML = MMLSemantics(w)
    //     include .sfol.SFOLEQ = kripke.SFOLSemantics(w)
    // }
}