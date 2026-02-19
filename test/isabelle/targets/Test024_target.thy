theory Test024_target
  imports Main "HOL-Library.FSet"
begin

definition u1 :: "int fset" where "u1 = {|1, 2, 3|}"
definition u2 :: "int fset" where "u2 = finsert 0 u1"
definition u3 :: "int fset" where "u3 = u1 |\<union>| {|3, 4|}" (* Duplicates automatically merged *)

end