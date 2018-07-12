import data.equiv.basic

namespace equiv

@[simp] lemma symm_comp_self_eq_id {α β : Sort*} (e : α ≃ β) : e.symm ∘ e = id :=
function.left_inverse.comp_eq_id e.left_inverse_symm

@[simp] lemma self_comp_symm_eq_id {α β : Sort*} (e : α ≃ β) : e ∘ e.symm = id :=
function.right_inverse.comp_eq_id e.right_inverse_symm

-- This definition has the advantage that (subtype_equiv_subtype h ap).val
-- reduces to ap.val.
def subtype_equiv_subtype {α : Sort*} {p p' : α → Prop} (h : p = p') :
  {a // p a} ≃ {a // p' a} :=
{ to_fun := λ ap, ⟨ap.val, h ▸ ap.property⟩,
  inv_fun := λ ap', ⟨ap'.val, h.symm ▸ ap'.property⟩,
  left_inv := λ ⟨a, p⟩, rfl,
  right_inv := λ ⟨a, p'⟩, rfl }

def subtype_prod_subtype_equiv_subtype {α β : Type*} {p : α → Prop} {q : β → Prop} :
  ({a // p a} × {b // q b}) ≃ {c : α × β // p c.1 ∧ q c.2} :=
⟨λ apbq, ⟨(apbq.fst.val, apbq.snd.val), ⟨apbq.fst.property, apbq.snd.property⟩⟩,
 λ abpq, (⟨abpq.val.fst, abpq.property.left⟩, ⟨abpq.val.snd, abpq.property.right⟩),
 λ ⟨⟨a, p⟩, ⟨b, q⟩⟩, rfl,
 λ ⟨⟨a, b⟩, ⟨p, q⟩⟩, rfl⟩

def replace_to_fun {α β : Sort*} (e : α ≃ β) (f : α → β) (h : ⇑e = f) : α ≃ β :=
{ to_fun := f,
  inv_fun := e.inv_fun,
  left_inv := h ▸ e.left_inv,
  right_inv := h ▸ e.right_inv }

end equiv
