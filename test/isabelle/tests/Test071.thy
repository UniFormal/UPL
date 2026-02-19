theory Test071
  imports Main
begin

definition t2 :: "int \<times> int" where
  "t2 = (1,2)"
definition t_21 :: "int" where
  "t_21 = fst (t2)"
definition t_22 :: "int" where
  "t_22 = snd (t2)"

end