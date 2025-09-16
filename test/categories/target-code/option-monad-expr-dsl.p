module DivLan {

    // DSL
    theory Val {
        n: int
    }
    theory Div {
        include Expr
        e1: expr
        e2: expr
    }
    theory Expr {
        include Val
        include Div
        type expr
        // actually want e: Val | Div (Union type)
        // workaround: abstract instance where either ev or ed has concrete value
        ev: Val
        ed: Div
    }

    // values of Expr
    expr1: expr = Expr {ed = Div { e1 = Expr {ev = Val {n=6}}, e2 = Expr {ev = Val {n=2}}}}
    expr2: expr = Expr {ed = Div { e1 = Expr {ev = Val {n=3}}, e2 = Expr {ev = Val {n=0}}}}

    // safe division function
    safediv: int -> int -> Option[int] = x -> y -> if (y==0) None else Some(x/y)

    // eval function, with bind infix operator/prefix function
    eval1: expr -> Option[int] = (e:expr) -> {
        if (e is Val) Some(e.ev.n}
        // bind :: Option[int] -> (int -> Option[int]) -> Option[int]
        else monad.bind(eval(e.ed.e1))((x:int) ->
                monad.bind(eval(e.ed.e2))((y:int) ->
                    safediv(x,y)))
    }

    // eval function, with do notation/-= notation
    eval2: expr -> Option[int] = (e:expr) -> {
        if (e is Val) Some(e.ev.n}
        // bind :: Option[int] -> (int -> Option[int]) -> Option[int]
        else do {
            x -= eval(e.ed.e1)
            y -= eval(e.ed.e2)
            safediv(x,y)
        }
    }
}