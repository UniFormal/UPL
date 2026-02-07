theory Test103_target
  imports Main
begin

locale partial_order =
  fixes le :: "'a ⇒ 'a ⇒ bool" (infixl ‹⊑› 50)
  assumes refl [intro, simp]: "x ⊑ x"
    and anti_sym [intro]: "⟦ x ⊑ y; y ⊑ x ⟧ ⟹ x = y"
    and trans [trans]: "⟦ x ⊑ y; y ⊑ z ⟧ ⟹ x ⊑ z"

locale total_order = partial_order +
  assumes total: "x ⊑ y ∨ y ⊑ x"


end