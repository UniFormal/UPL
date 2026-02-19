theory Test310
  imports Main
begin

fun map2 :: "int list => ((int => int) => int list)" where
"map2 [] f = None"
| "map2 (x # xs) f = ((f x) # (map2 xs) f)"

end