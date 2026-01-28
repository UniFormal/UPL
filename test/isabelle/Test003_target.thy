
theory Test3_target
  imports Main
begin


type_synonym number = nat
type_synonym gate = "bool \<Rightarrow> bool \<Rightarrow> bool"
type_synonym ('a, 'b) alist = "('a \<times> 'b) list"

typedecl b

end