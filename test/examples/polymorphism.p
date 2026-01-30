module Polymorphism {
  // Shallow/Rank-1/toplevel polymorphism: type variables are allowed at the toplevel of a symbol declaration.
  // This constraint is hard-coded into the syntax: there are no binders for type variables, e.g., no type-label lambdas or universal quantifier over types.
  // Instead, every symbol declaration may take variables following its name.
  // References to such symbols must accordingly be followed by types.

  // Type and expression declarations may by polymorphic, i.e., take type variables using @(A1,...,An). The brackets are optional for a single argument.
  // These type variables may occur in the subsequent parts of the declaration.
  // Polymorphic symbols must only be used in fully applied form, also via @(T1,...,Tn). They are not well-formed objects on their own.

  // polymorphic identity function
  id@A: A -> A = x -> x
  // polymorphic function composition
  comp@(A,B,C)(f: A -> B, g: B -> C) = x -> g(f(x))

  // The theory of an endofunctor on the category of types.
  theory TypeFunctor {
    // map types to types
    type typeApply@A
    // map functions to functions
    funApply@(A,B): (A -> B) -> (typeApply@A -> typeApply@B)

    // preservation of identity
    funApplyId@A: |- funApply(id) == id
    // preservation of composition
    funApplyComp@(A,B,C): |- forall f,g. funApply@(A,C)(comp(f,g)) == comp(funApply@(A,B)(f), funApply@(B,C)(g))
    // alternatively, we can give the variable types and infer the type arguments
    funApplyCompVar@(A,B,C): |- forall f: A->B, g:B->C. funApply(comp(f,g)) == comp(funApply(f), funApply(g)) = funApplyComp
  }

  // lists as such a functor
  List = TypeFunctor {
    type typeApply@A = list[A]
    funApply@(A,B) = f -> l -> {
      l match {
        [] -> []
        h -: t -> f(h) -: funApply(f)(t)  // if type arguments are omitted from an expression symbol, they are treated like @(_,...,_) and are inferred
      }
    }
    // omitted proofs
    funApplyId@A = ???
    funApplyComp@(A,B,C) = ???
  }

  test = {val l = list[1,2,3]; List.funApply(x -> x+1)(l) == [2,3,4]}
}