import data.equiv

namespace equiv

@[simp] lemma symm_comp_self_eq_id {α β : Sort*} (e : α ≃ β) : e.symm ∘ e = id :=
function.left_inverse.f_g_eq_id e.left_inverse_symm

@[simp] lemma self_comp_symm_eq_id {α β : Sort*} (e : α ≃ β) : e ∘ e.symm = id :=
function.right_inverse.g_f_eq_id e.right_inverse_symm

end equiv
