theory Test015x
  imports Main
begin

fun factorial2 :: "int => int" where
  factorial2 x = (if (x \<le> 0) then 1 else (x * factorial2 (x - 1))

end