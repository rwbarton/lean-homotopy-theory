import data.equiv.basic

universes u v w
variables {α : Sort u} {β : Sort v} {γ : Sort w}

-- A constructive version of `bijective`.
structure Is_equiv (f : α → β) :=
(e : α ≃ β)
(h : f = e)

instance (f : α → β) : subsingleton (Is_equiv f) :=
⟨begin
  intros e e',
  cases e with ee eh, cases e' with e'e e'h,
  have : ee = e'e, from equiv.eq_of_to_fun_eq (by cc),
  cc
end⟩

lemma Is_equiv.bijective {f : α → β} (e : Is_equiv f) : function.bijective f :=
by rw e.h; exact e.e.bijective

lemma Is_equiv.cancel_left {f : α → β} (e : Is_equiv f) {a : α} :
  e.e.inv_fun (f a) = a :=
by rw [e.h] { occs := occurrences.pos [2] }; exact e.e.left_inv a

lemma Is_equiv.cancel_right {f : α → β} (e : Is_equiv f) {b : β} :
  f (e.e.inv_fun b) = b :=
by rw [e.h] { occs := occurrences.pos [1] }; exact e.e.right_inv b
