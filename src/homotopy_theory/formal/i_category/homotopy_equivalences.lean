import .homotopy_classes

universes u v

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
-- Homotopy equivalences as the weak equivalences of an I-category.
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

instance homotopy_category.category_with_weak_equivalences :
  category_with_weak_equivalences (category_mod_congruence C homotopy_congruence) :=
isomorphisms_as_weak_equivalences

instance I_category.category_with_weak_equivalences : category_with_weak_equivalences C :=
preimage_with_weak_equivalences (quotient_functor C homotopy_congruence)

def homotopy_equivalence {x y : C} (f : x ⟶ y) : Prop := is_weq f

lemma homotopic_iff_equal_in_ho {x y : C} {f g : x ⟶ y} : f ≃ g ↔ ⟦f⟧ = ⟦g⟧ :=
by symmetry; apply quotient.eq

lemma homotopy_equivalence_iff {x y : C} {f : x ⟶ y} :
  homotopy_equivalence f ↔ ∃ g, g ∘ f ≃ 𝟙 _ ∧ f ∘ g ≃ 𝟙 _ :=
begin
  split,
  { intro h, cases h with i hi,
    cases quotient.exists_rep i.inv with g hg,
    existsi g, split; rw homotopic_iff_equal_in_ho,
    { have := i.hom_inv_id,
      rw [hi, ←hg] at this, exact this },
    { have := i.inv_hom_id,
      rw [hi, ←hg] at this, exact this } },
  { intro h, rcases h with ⟨g, h₁, h₂⟩,
    refine ⟨iso.mk ⟦f⟧ ⟦g⟧ _ _, rfl⟩;
    { dsimp [auto_param], change ⟦_⟧ = ⟦_⟧, rw ←homotopic_iff_equal_in_ho,
      exact h₁ <|> exact h₂ } }
end

end homotopy_theory.cofibrations
