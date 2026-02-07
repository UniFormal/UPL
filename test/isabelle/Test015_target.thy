theory Test014
  imports Main
begin

fun f :: "int => int" where
  "f x = x"
fun g :: "int => int => int" where
  "g x y = (x + y)"
fun h :: "int => int => bool => bool" where
  "h x y z = z"
fun i :: "int => int => int" where
  "i x y = (x + y)"

end