import algebra.order_functions

universe u
variable {α : Type u}

section decidable_linear_ordered_comm_group
variables [decidable_linear_ordered_comm_group α] {a b c : α}

lemma abs_eq (hb : b ≥ 0) : abs a = b ↔ a = b ∨ a = -b :=
iff.intro
  begin
    cases le_total a 0 with a_nonpos a_nonneg,
    { rw [abs_of_nonpos a_nonpos, neg_eq_iff_neg_eq, eq_comm], exact or.inr },
    { rw [abs_of_nonneg a_nonneg, eq_comm], exact or.inl },
  end
  (by intro h; cases h; subst h; try { rw abs_neg }; exact abs_of_nonneg hb)

end decidable_linear_ordered_comm_group
