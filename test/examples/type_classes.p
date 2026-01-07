module TypeClasses {
  // The name "univ" is special: any use of an instance of the theory is converted to a type by projecting out univ.

  // That allows representing type classes as theories with a type "univ", e.g.,
  theory Magma {
    type univ
    op: (univ,univ) -> univ # infix ∘
    double: univ -> univ # prefix $ = x -> x∘x
  }
  // That allows using instances of the type class as if they were types.
  // Notations are disambiguated by using the argument or expected types if those are C.a for some type a declared in C.
  isHom(M,N:: Magma, f:M -> N) = forall x,y. f(x∘y)==f(x)∘f(y)
  // The type of f is actually M.univ -> N.univ.f
  // The expected type of x∘y is M.univ, which finds the notation for ∘ in the type Magma of M.
  // Then x∘y is elaborated into M.op(x,y).
  // That allows infering the types of x and y.

  // Extensions of type classes with definitions or theorems can be made as definitions inside the class (like double above and least below)
  // or outside as functions that take an instance as an additional arguments (like isNeut and double_double below).

  isNeut(M:Magma, e:M) = forall x. e∘x==x & x∘e==x
  double_double = (M:Magma,x:M) -> $ $x // $$x does not work because $$ would be parsed as a single operator

  // This also works when using include/realize.
  theory Compare {
    type univ
    compare: (univ,univ) -> bool # infix <<
    least: univ -> bool = x -> forall y. x << y
  }
 
  theory Factoring {
    include Magma
    realize Compare
    compare(x,z::_) = exists y. x∘y==z
  }

  // extension of Factoring with a theorem (with ??? for an omitted proof):
  neutLeast1: (F: Factoring) -> |- (forall e. isNeut(F,e) => F.least(e)) = ???
  // the same, with definitions expanded:
  neutLeast2: (F: Factoring) -> |- (forall e:F. (forall x. e∘x==x & x∘e==x) => forall x. e<<x) = ???
}