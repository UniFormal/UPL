module M {
  class Person {
    name: string
    age: int
  }
  class Gendered : Person {
    male: bool
    age = 5
    address = (if male "Mr" else "Mrs") + " " + name
  }
  f: int -> Person
  g = f(0)
}
