module kripke_dynamic {
    // a theory of states, i.e. assignments to program variables
    theory State {
        include .hol.HOL
        include .kripke.Worlds
        cell: tp -> tp
        state: tm world -> (S: tp) -> tm (cell S) -> tm S

        extends: tm world -> tm world -> (S: tp) -> tm (cell S) -> (tm world -> tm S) -> prop
            = v -> w -> S -> n -> x -> and(tequal(S, state w S n, x v),
                                           tforall (cell S) (m -> impl(not(tequal(cell S, n, m)),
                                                                       tequal(S, state v S m, state w S m))))

        trclos: (S: tp) -> (tm S -> tm S -> prop) -> tm S -> tm S -> prop
        trclose_extend: (S, r) -> (x, y) -> ded (r x y) -> ded (trclos S r x y)
        trclose_refl: (S, r) -> x -> ded (trclos S r x x)
        trclose_trans: (S, r) -> (x, y, z) -> ded (trclos S r x y) -> ded (trclos S r y z) -> ded (trclos S r x z)
    }

    // The views below need defined includes (include X = Y). Written as `s -> T { ... }`
    // they cannot even parse, because the T{decls} form filters the body down to symbol
    // declarations. Use the anonymous-theory form `s -> §{ include T ... }` instead, which
    // keeps includes. They are still commented out because they bottom out in
    // kripke.LogicSemantics / PLSemantics / SFOLSemantics and kripke_multimodal.MMLSemantics,
    // which are blocked by the checker issues documented in kripke.p.

    // Dynamic logic is the multimodal logic whose modalities are programs,
    // interpreted as state-transition relations.
    // DynamicLogicSemantics: State -> .dynamic.DynamicLogic = s -> §{
    //     include .multimodal.MML = .kripke_multimodal.MMLSemantics(s)
    // }

    // NonDetProgSemantics: State -> .dynamic.NonDetProg = s -> .dynamic.NonDetProg {
    //     include .dynamic.Programs = DynamicLogicSemantics(s)
    //     include .pl.PL = .kripke.PLSemantics(s)

    //     comp = (p, q) -> u -> w -> texists world (v -> and(p u v, q v w))
    //     distrib = (p, q) -> v -> w -> or(p v w, q v w)
    //     iteration = p -> v -> w -> trclos world p v w
    //     test = f -> v -> w -> and(f v, tequal(world, v, w))
    //     skip = v -> w -> tequal(world, v, w)
    // }

    // PropDynamicLogicSemantics: State -> .dynamic.PropDynamicLogic = s -> .dynamic.PropDynamicLogic {
    //     include .dynamic.DynamicLogic = DynamicLogicSemantics(s)
    //     include .dynamic.NonDetProg = NonDetProgSemantics(s)
    // }

    // TypedDynamicSemantics: State -> .dynamic.TypedDynamicLogic = s -> .dynamic.TypedDynamicLogic {
    //     include .dynamic.PropDynamicLogic = PropDynamicLogicSemantics(s)
    //     include .sfol.SFOLEQ = .kripke.SFOLSemantics(s)

    //     type varDL(S: tp) = tm (cell S)
    //     retrieve = S -> n -> w -> state w S n
    //     assign = S -> n -> x -> v -> w -> extends v w S n x
    //     random_assign = S -> n -> v -> w -> texists (simpfun(world, S)) (t -> extends v w S n (u -> apply1(world, S) t u))
    // }
}
