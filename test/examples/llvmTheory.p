module Theories {


  // theories work like classes or record types
  theory Person {
    // In a theory, declarations may undefined (abstract) or defined (concrete).
    name: string
    age: int
    someOtherValue: int
    male: bool
    address = (if (male) "Mr" else "Mrs") + " " + name
  }
  theory Man {
    // Theories may be included into other modules/theories.
    include Person
    // All included and local declarations are collected. Declarations for the same name are merged.
    // Previous declarations are used to obtain the expected type.
    male = true
    age = 100
    someOtherValue = 20
  }


  // Theories may contain type declarations. In that case, the resulting type is big, i.e. limited in its use.
  theory Magma {
    type univ
    op: (univ,univ) -> univ
  }
