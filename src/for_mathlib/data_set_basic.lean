import data.set.basic

open set

namespace set
-- near range_id
variables {α : Type*}
@[simp] theorem range_subtype_val {p : α → Prop} : range (@subtype.val α p) = set_of p :=
set.ext $ by simp

-- where?
-- Also, use it in embedding_subtype_val
theorem injective_subtype_val {p : α → Prop} : function.injective (@subtype.val α p) :=
assume a₁ a₂ h, subtype.eq h

lemma diff_subset_iff {s t u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
⟨assume h x xs, classical.by_cases or.inl (assume nxt, or.inr (h ⟨xs, nxt⟩)),
 assume h x ⟨xs, nxt⟩, or.resolve_left (h xs) nxt⟩

lemma diff_subset_comm {s t u : set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
by rw [diff_subset_iff, diff_subset_iff, union_comm]

end set
