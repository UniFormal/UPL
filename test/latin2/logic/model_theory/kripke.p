module kripke {
    theory Worlds {
        include .hol.HOLND

        world: tp // # W

        liftPred2: (S, A, B) -> (tm A -> tm B -> prop) -> (tm S -> tm A) -> (tm S -> tm B) -> tm S -> prop
            = (S, A, B) -> o -> f -> g -> x -> o (f x) (g x)
            // # liftFun2 4

        lift0: S -> prop -> tm S -> prop
            = S -> o -> x -> o
            // # lift0 2

        lift1: S -> (prop -> prop) -> (tm S -> prop) -> tm S -> prop
            = S -> o -> f -> x -> o (f x)
            // # lift1 2

        lift2: S -> (prop -> prop -> prop) -> (tm S -> prop) -> (tm S -> prop) -> tm S -> prop
            = S -> o -> f -> g -> x -> o (f x) (g x)
            // # lift2 2

        liftbind: S -> (T -> (tm T -> prop) -> prop) -> T -> ((tm S -> tm T) -> tm S -> prop) -> tm S -> prop
            = S -> B -> T -> F -> x -> B (simpfun(S, T)) (f -> F (apply1(S, T) f) x)
            // # liftbind 2
    }

    theory KripkeFrame {
        include .base_languages.TypedLogic
        include Worlds

        accessible: tm world -> tm world -> prop
    }

    theory KripkeModel {
        include .sfol.SFOLEQ
        include KripkeFrame
    }

    PropSemantics: Worlds -> .concepts.Propositions = w -> .concepts.Propositions {
        type prop = w{tm world} -> w.prop
    }

    // NOTE on the commented-out views below.
    // The reason they cannot be written as `w -> T { ... }` is that the `T{decls}` form
    // drops includes: the parser filters the body down to symbol declarations and reports
    // "symbol declaration expected" for `include X = Y` (Parser.scala, the M{decls} branch).
    // The anonymous-theory form `§{ ... }` does NOT filter, so defined includes are accepted:
    LogicSemantics: Worlds -> .concepts.Logic = w -> §{
        include .concepts.Logic
        include .concepts.Propositions = PropSemantics(w)
        // Blocked: writing the intended `(x) -> w{ded (p x)}` reports "prop: illegal type",
        // because in an instance body a parametric declaration may not refer to a type
        // defined in that same body. Left as a hole, which is why consumers of this view
        // report "missing definition of ded".
        type ded(p: prop) = ??? // (x) -> w{ded (p x)}
    }
    // That much is verified. What still blocks these particular views are checker
    // limitations around owners/quotations:
    //  1. For an inherited parametric type declaration such as `type ded(p: prop)`, the
    //     parameter type `prop` is resolved in the *target's* context, so `p` always ends up
    //     with w's `prop` (tm boolean) rather than the view's translated `prop`. Tried with
    //     prop translated as `w{tm world} -> w.prop`, `w{tm (world → boolean)}` and
    //     `w{tm world -> prop}`; all give "found: tm(boolean)". This is also why
    //     pl_tableaux.Proofs2Tableaux works: there `type prop = t.prop` is identity-like,
    //     so resolving `prop` in the target happens to be correct.
    //  2. `Eval` (backtick), which would splice an outer expression into a quotation, is
    //     parser-gated to non-type positions, so it cannot repair (1) inside a type.
    //  3. Instantiating a quoted polymorphic function at an owned type yields ill-formed
    //     types, e.g. `w{lift0 world truth}` reports "tm(w{world}): illegal type".
    // Independently of the tool: Worlds.lift1/lift2 take *curried* operators
    // (prop -> prop -> prop) while pl.and/or/impl/equiv are tuple-typed ((prop, prop) -> prop),
    // so those assignments need eta-expansion, e.g. `lift2 world (a -> b -> and(a, b))`.

    // PLSemantics: Worlds -> .pl.PL = w -> §{
    //     // KNOWN BLOCKER, and the only error left in this view: normalizing an owned type
    //     // that applies a type former to a field of the owner distributes the owner inward,
    //     // so `w{tm world}` becomes the ill-formed `tm(w{world})` ("illegal type").
    //     // Same for `w{tm world -> prop}` and for naming the type inside Worlds and using
    //     // w{...} or w.<name>. The connective assignments below are otherwise correct.
    //     //type prop = w{tm world} -> w.prop
    //     include .concepts.Propositions = PropSemantics(w)

    //     truth = x -> w{truth}
    //     falsity = x -> w{falsity}
    //     and = (F, G) -> x -> w{and(`F x`, `G x`)}
    //     or = (F, G) -> x -> w{or(`F x`, `G x`)}
    //     impl = (F, G) -> x -> w{impl(`F x`, `G x`)}
    //     not = F -> x -> w{not(`F x`)}
    //     equiv = (F, G) -> x -> w{equiv(`F x`, `G x`)}
    // }

    // PLHilbertSemantics: Worlds -> .pl_hilbert.PLHilbert = w -> .pl_hilbert.PLHilbert {
    //     include .concepts.Propositions = PropSemantics(w)
    //     include .concepts.Logic = LogicSemantics(w)
    //     include .pl.PL = PLSemantics(w)

    //     trueI = w -> trueI

    //     falseE = f -> (g, w) -> falseE (f w) inconE

    //     andI = (F, G, f, g) -> w -> andI (f w) (g w)
    //     andEl = (F, G, fg) -> w -> andEl (fg w)
    //     andEr = (F, G, fg) -> w -> andEr (fg w)
    //     orIl = (F, G, f) -> w -> orIl (f w)
    //     orIr = (F, G, f) -> w -> orIr (f w)
    //     orE_ax = (F, G, H) -> w -> orE_ax

    //     implE = (F, G, fg, f) -> w -> implE (fg w) (f w)
    //     K_ax = (F, G, w) -> K_ax
    //     S_ax = (F, G, H, w) -> S_ax

    //     notI_ax = (F, w) -> notI_ax
    //     notE = (F, nf, f) -> (g, w) -> inconE (notE (nf w) (f w))

    //     equivI_ax = (F, G, w) -> equivI_ax
    //     equivEl = (F, G, fg, f) -> w -> equivEl (fg w) (f w)
    //     equivEr = (F, G, fg, g) -> w -> equivEr (fg w) (g w)

    //     classical = (F, p) -> w -> classical (Fwincon -> A -> p (Fw -> Gv -> v -> Fwincon (Fw w) (Gv v)) (u -> A) w)
    // }

    TermSemantics: Worlds -> .concepts.TypedTerms = w -> .concepts.TypedTerms {
        // constant universe; alternative would be tp = tm W -> tp
        type tp = tp
        type tm(a: tp) = w{tm world} -> w{tm a}
    }

    // SFOLSemantics: Worlds -> .sfol.SFOLEQ = w -> .sfol.SFOLEQ {
    //     include .concepts.TypedTerms = TermSemantics(w)
    //     include .pl.PL = PLSemantics(w)
    //     include .concepts.Logic = LogicSemantics(w)

    //     tforall = A -> liftbind world tforall A
    //     texists = A -> liftbind world texists A
    //     tequal = S -> liftPred2 world S S (tequal S)
    // }

    // MLSemantics: KripkeModel -> .ml.ML = w -> .ml.ML {
    //     include .pl.PL = PLSemantics(w)
    //     include .concepts.Logic = LogicSemantics(w)

    //     box = p -> v -> tforall world (w -> impl (accessible v w, p w))
    //     diamond = p -> v -> texists world (w -> and (accessible v w, p w))
    // }

    // MLHilbertSemantics: KripkeModel -> .ml_hilbert.MLHilbert = w -> .ml_hilbert.MLHilbert {
    //     include .ml.ML = MLSemantics(w)
    //     include .pl_hilbert.PLHilbert = PLHilbertSemantics(w)
    // }
}



    
