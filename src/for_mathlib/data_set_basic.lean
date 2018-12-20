import data.set.basic

attribute [simp] set.subtype_val_range

universes u v w

open set

lemma factors_iff {α : Type u} {β : Type v} {γ : Type w} (f : α → γ) (g : β → γ) :
  (∃ h, f = g ∘ h) ↔ range f ⊆ range g :=
⟨by rintros ⟨h, rfl⟩ _ ⟨a, rfl⟩; use h a,
 λ H, by choose h hh using H; exact ⟨λ a, h ⟨a, rfl⟩, funext $ λ a, (hh ⟨a, rfl⟩).symm⟩⟩
