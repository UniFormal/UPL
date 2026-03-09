theory Test042_target
  imports Main
begin

definition b :: bool where
"b = True"

theorem t: "b"
  apply(auto)
  done



end