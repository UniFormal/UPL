module drt_fol {
    // The semantics of DRT is traditionally given in form of a translation to 
    // First-Order Logic. Here we try to give that as a view. But this does not work yet. 
    // But we record the idea in any case.

    DRTFOL: .fol.FOL -> .drt.DRT = f -> .drt.DRT {
        dr = f.term
        mode = f.term
        pos = (x) -> x
        neg = (x) -> x
        empty = ???
        punion = (x,y) -> ???
        mequal = (x,y) -> ⊤
        capture = (x,y) -> ⊤
        close = (x) -> x

        drs = (m) -> f.prop
        cond = (m) -> f.prop
        tm = (m) -> f.term

        atomic = (m,n) -> (c) -> ∃m. c
        merge = (m,n) -> (d,e) -> ??? // this should never occur in normalized DRSs
        dneg = (m) -> d -> ¬d
        dimpl = (m,n) -> (d,e) -> (∀m. d) ⇒ (∃n. e)
    }
}