theory Test042
  imports Main
begin

definition b :: "bool" where
  "b = True"
theorem axiom_outside_theory: "b"
apply(auto)
done

end