theory Test1
  imports Main
begin

definition a :: bool where
  "a = (True \<and> False)"
definition b :: bool where
  "b = (True \<or> False)"
definition c :: bool where
  "c = (\<not> False)"
definition d :: bool where
  "d = (False \<longrightarrow> True)"
definition e :: bool where
  "e = (1 < 2)"
definition f :: bool where
  "f = (1 \<le> 2)"
definition n :: int where
  "n = (1 + 2)"

end