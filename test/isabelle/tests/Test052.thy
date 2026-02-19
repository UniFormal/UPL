theory Test052
  imports Main
begin

definition i :: "int" where
  "i = (min 10 (- 10))"
definition j :: "int" where
  "j = (max 10 (- 10))"

end