import data.sum
import data.set

open sum

lemma preimage_inl_image_inl {α β : Type*} (u : set α) :
  @inl α β ⁻¹' (@inl α β '' u) = u :=
set.preimage_image_eq u (λ _ _, inl.inj_iff.mp)

lemma preimage_inl_image_inr {α β : Type*} (u : set β) :
  @inl α β ⁻¹' (@inr α β '' u) = ∅ :=
set.eq_empty_iff_forall_not_mem.mpr (assume b ⟨a, _, h⟩, inr_ne_inl h)

lemma preimage_inr_image_inl {α β : Type*} (u : set α) :
  @inr α β ⁻¹' (@inl α β '' u) = ∅ :=
set.eq_empty_iff_forall_not_mem.mpr (assume a ⟨b, _, h⟩, inl_ne_inr h)

lemma preimage_inr_image_inr {α β : Type*} (u : set β) :
  @inr α β ⁻¹' (@inr α β '' u) = u :=
set.preimage_image_eq u (λ _ _, inr.inj_iff.mp)
