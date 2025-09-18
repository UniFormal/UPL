module EvalWithState {

    // expression language
    datatype Expr = Val(int) | Div(Expr, Expr)

    // -------------------------------------------------
    // THEORY: about evaluation and counting divisions
    // -------------------------------------------------
    theory EvalCounter {
        // Abstract set of evaluations: (Expr, Result, Count)
        evals: set[(Expr, int, int)]

        // Axiom: if (e, v, c) ∈ evals, then
        // evaluating expression e yields result v
        // and c is the number of Div-nodes visited
        eval_ax: |-
          forall triple in evals.
            match triple(1) with {
              case Val(n) => triple(2) == n ∧ triple(3) == 0
              case Div(e1, e2) =>
                exists v1, c1, v2, c2.
                  ( (e1, v1, c1) ∈ evals ∧
                    (e2, v2, c2) ∈ evals ∧
                    triple(2) == v1 / v2 ∧
                    triple(3) == c1 + c2 + 1 )
            }
    }

    // -------------------------------------------------
    // IMPLEMENTATION: evaluation with state monad
    // -------------------------------------------------
    def tick : State[Int, Unit] =
      do { s <- getState
           putState(s + 1)
           return ()
      }

    def eval(e : Expr) : State[Int, Int] =
      match e with {
        case Val(n) =>
          return n

        case Div(e1, e2) =>
          do { m <- eval(e1)
               n <- eval(e2)
               tick
               return (m / n)
          }
      }

    // -------------------------------------------------
    // CONCRETE EXAMPLE
    // -------------------------------------------------
    expr1 = Div(Val(6), Div(Val(2), Val(1)))

    run1 = runState(eval(expr1), 0)
    // should yield (6, 2): result 6, counter 2

    evalCounterExample = EvalCounter {
      evals = {(expr1, 6, 2)}
      eval_ax = ???    // here you link the axiom to computation
    }
}
