module Theories {
  // theories work like classes or record types
  theory Person {
    // In a theory, declarations may undefined (abstract) or defined (concrete).
    name: string
    age: int
    male: bool
    address = (if (male) "Mr" else "Mrs") + " " + name
  }

  theory Man {
    // Theories may be included into other modules/theories.
    include Person
    // All included and local declarations are collected. Declarations for the same name are merged.
    // Previous declarations are used to obtain the expected type.
    male = true
  }
  // Theories are abstract if any field is, otherwise concrete.

  // Theories can be turned into types and expressions.
  // For every theory T, there is the type Mod(T) of models of T.
  // For every concrete theory U that extends T, there is the expression mod(U) of type Mod(T).
  // In surface syntax mod(-) and Mod(-) are not written.

  // Thus, every theory can be used as the type of its models.
  // To obtain a concrete theory as an expression of type Mod(T),
  // the notation T{b} can be used where b defines the remaining abstract fields.
  // This corresponds to creating a new instance of a class. No 'new' keyword is used.
  me = Man {name = "Florian", age = 45}

  // Theories may contain type declarations. In that case, the resulting type is big, i.e., limited in its use.
  theory Magma {
    type u
    op: (u,u) -> u
  }

  // For a Boolean b, the type |- b is the type of proofs of b.
  // That can be used to declare axioms.
  theory Semigroup  {
    include Magma
    assoc: |- forall x,y,z. op(op(x,y),z) == op(x,op(y,z))
  }
  theory Commutative {
    include Magma
    comm: |- forall x,y. op(x,y) == op(y,x)
  }
  theory Monoid  {
    include Semigroup
    e: u
    neutral: |- forall x. op(x,e) == x & op(e,x) == x
  }
  // Multiple includes of the same theories (diamonds) are identified.
  theory CommutativeMonoid {
    include Monoid
    include Commutative
  }
  // When instantiating, ??? can be used for unknown terms. If there are not computational, like proofs, this is harmless.
  intAdd = Semigroup {
    type u = int
    op(x,y::_) = x+y
    assoc = ???
  }

  // When merging declarations, the second declaration can be more restrictive:
  theory IntMagma {
    include Magma
    type u < int // refining a type to be a subtype
  }
  theory IntMagma2 {
    include Magma
    type u = int // maximally refine a type by defining it
  }

  // The keyword "realize" behaves like "include" except that it additionally checks that all included declarations are defined.
  theory Pointed {
    type u
    point: u
  }
  theory NeutralPoint {
    include Monoid
    realize Pointed // This yields a second declaration "type u". Both are merged.
    point = e // Without this, Pointed would be fully realized.
    // Declarations present in both the realizing and the realized theory (here: u) do not have to be defined.
  }
}