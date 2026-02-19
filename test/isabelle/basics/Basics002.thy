theory Basics002
  imports Main
begin

definition t :: "int \<times> char list" where
  "t = (1,''foo'')"
definition t_1 :: "int" where
  "t_1 = fst (t)"

end