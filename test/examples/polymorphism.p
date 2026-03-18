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
    type univ@A
    // map functions to functions
    map@(A,B): (A -> B) -> (univ@A -> univ@B)

    // preservation of identity
    mapId@A: |- map(id) == id
    // preservation of composition
    mapComp@(A,B,C): |- forall f,g. map@(A,C)(comp(f,g)) == comp(map@(A,B)(f), map@(B,C)(g))
    // alternatively, we can give the variable types and infer the type arguments
    mapCompVar@(A,B,C): |- forall f: A->B, g:B->C. map(comp(f,g)) == comp(map(f), map(g)) = mapComp
  }

  theory Monad {
    include TypeFunctor
    
    embed@A: A -> univ@A # prefix !
    flatten@A: univ@(univ@A) -> univ@A

    bind@(A,B): univ@A -> (A -> univ@B) -> univ@B # infix >>=
              = x -> f -> flatten(map(f)(x))
  }

  // lists as such a functor
  List = Monad {
    type univ@A = list[A]
    map@(A,B) = f -> l -> {
      l match {
        [] -> []
        h -: t -> f(h) -: map(f)(t)  // if type arguments are omitted from an expression symbol, they are treated like @(_,...,_) and are inferred
      }
    }
    embed@A = x -> [x]
    flatten@A = ls -> ls match {
      [] -> []
      h -: t -> h ::: flatten(t)
    }
    // omitted proofs
    mapId@A = ???
    mapComp@(A,B,C) = ???
  }


  test = {val l = list[1,2,3]; List.map(x -> x+1)(l) == [2,3,4]} 
        // {val l: List{univ@int} = [1,2]; List.bind(l)(x -> [x,x]) == [1,1,2,2]}
  
}