import category_theory.isomorphism

-- Restore commented-out simp lemmas from category_theory.isomorphism.
-- TODO: Re-upstream these or generate them automatically?

universes u v

namespace category_theory

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

namespace iso

-- These lemmas are quite common, to help us avoid having to muck around with associativity.
-- If anyone has a suggestion for automating them away, I would be very appreciative.
@[simp] lemma hom_inv_id_assoc_lemma (I : X ≅ Y) (f : X ⟶ Z) : I.hom ≫ I.inv ≫ f = f :=
begin
  -- `obviously'` says:
  rw [←category.assoc, iso.hom_inv_id, category.id_comp]
end

@[simp] lemma inv_hom_id_assoc_lemma (I : X ≅ Y) (f : Y ⟶ Z) : I.inv ≫ I.hom ≫ f = f :=
begin
  -- `obviously'` says:
  rw [←category.assoc, iso.inv_hom_id, category.id_comp]
end

end iso

end category_theory
