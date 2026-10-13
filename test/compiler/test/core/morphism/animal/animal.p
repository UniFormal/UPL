theory Animal { name: string, legs: int }

theory Pet { owner: string }

theory Dog {
  include Animal,  include Pet
  legs = 4, breed: string
}

say_hello = (x:Animal) -> {
  Uniformal.print(x.name)
}

milo = Dog {name = "Milo", owner = "Jannes", breed = "Labrador"}
charlie = Animal {name = "Charlie", legs = 0}
