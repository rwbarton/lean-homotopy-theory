import .homotopy_equivalences
import .lemmas

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

/-

We show that IA is a cylinder object for A, in the sense that
A ⊔ A → IA → A is a factorization of the fold map into a
cofibration followed by a homotopy equivalence.

-/

namespace homotopy_theory.cofibrations
section C
open category_theory.has_initial_object
open homotopy_theory.cylinder
open I_category

parameters {C : Type u} [category.{v+1} C] [has_initial_object.{v} C]
  [has_coproducts.{v} C] [Icat : I_category.{v} C]
include Icat

lemma cof_ii (a : C) : is_cof (ii.{v} @> a) :=
begin
  let po :=
    (Is_pushout_of_isomorphic (Is_pushout.refl (! (∂I.obj a))) _ _
      (coprod_initial_right ∅).symm (iso.refl _)
      (initial_object.unique Ii_initial (initial_object.{v} C).is_initial_object)
      _ _),
  convert relative_cylinder' (! a) (all_objects_cofibrant.cofibrant.{v} a) _ _ po,
  any_goals { apply coprod.uniqueness; apply initial.uniqueness },
  symmetry,
  convert ←(po.induced_commutes₀ _ _ _),
  convert id_comp _ _,
  simp
end

lemma i₀p {a : C} : i.{v} 0 @> a ∘ p @> a ≃ 𝟙 (I.obj a) :=
let ⟨J, hJ₁, hJ₂⟩ :=
  hep_cof (ii.{v} @> a) (cof_ii a) 0 (I.obj a) (i 0 @> a ∘ p @> a)
    (I_of_coprod_is_coproduct.induced (i 0 @> a ∘ p @> a) (𝟙 (I.obj a))) $ begin
      apply coprod.uniqueness; erw i_nat_assoc; simp,
      rw ←assoc, dsimp, simp
    end in
⟨⟨J ∘ T @> a,
  begin
    erw [←assoc, cylinder_has_interchange.Ti],
    have : J ∘ I &> (i 0 @> a) = J ∘ I &> (ii @> a ∘ i₀), by simp [ii], rw this,
    rw [I.map_comp, assoc, hJ₂], simp
  end,
  begin
    erw [←assoc, cylinder_has_interchange.Ti],
    have : J ∘ I &> (i 1 @> a) = J ∘ I &> (ii @> a ∘ i₁), by simp [ii], rw this,
    rw [I.map_comp, assoc, hJ₂], simp
  end⟩⟩

lemma heq_p {a : C} : homotopy_equivalence.{v} (p @> a) :=
homotopy_equivalence_iff.mpr ⟨i 0 @> a, i₀p, by simp; refl⟩

lemma pii {a : C} : p.{v} @> a ∘ ii @> a = coprod.fold a :=
by apply coprod.uniqueness; simp

end C
end homotopy_theory.cofibrations
