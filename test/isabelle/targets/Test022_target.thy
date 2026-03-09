theory Test022_target
  imports Main
begin

definition s1 :: "int set" where "s1 = {1, 2, 3}"
definition s2 :: "int set" where "s2 = {x. x > 10}"      (* Set comprehension *)
definition s3 :: "int set" where "s3 = s1 \<union> {4, 5}"       (* Union *)
definition s4 :: "int set" where "s4 = {0..10}"           (* Interval set *)

end