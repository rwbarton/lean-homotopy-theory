import category_theory.colimit_lemmas
import .definitions

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open category_theory.has_initial_object category_theory.preserves_initial_object
open category_theory.preserves_coproducts
open homotopy_theory.cylinder
open I_category

variables {C : Type u} [category.{v} C] [has_initial_object.{v} C]
  [has_coproducts.{v} C] [Icat : I_category.{v} C]
include Icat

def Ii_initial : Is_initial_object.{v} (I.obj ∅ : C) :=
Is_initial_object_of_Is_initial_object
  has_initial_object.initial_object.is_initial_object

def I_preserves_coproducts : preserves_coproducts (I : C ↝ C) :=
⟨λ a₀ a₁ b f₀ f₁ copr,
  let po : Is_pushout (! a₀) (! a₁) f₀ f₁ :=
    Is_pushout_of_Is_coproduct_of_Is_initial copr
      has_initial_object.initial_object.is_initial_object in
  Is_coproduct_of_Is_pushout_of_Is_initial
    (I_preserves_pushout_by_cof (all_objects_cofibrant.cofibrant a₀) po) Ii_initial⟩

def I_of_coprod_is_coproduct {a₀ a₁ : C} :
  Is_coproduct (I &> (i₀ : a₀ ⟶ a₀ ⊔ a₁)) (I &> (i₁ : a₁ ⟶ a₀ ⊔ a₁)) :=
let ⟨f⟩ := I_preserves_coproducts in
f (has_coproducts.coproduct.{v} a₀ a₁).is_coproduct

lemma I_preserves_cofibrations {a b : C} {j : a ⟶ b} (hj : is_cof j) : is_cof (I.map j) :=
begin
  convert cof_comp _ (relative_cylinder j hj),
  exact (Is_pushout.induced_commutes₁ _ _ _ _).symm,
  exact precofibration_category.pushout_is_cof (pushout.is_pushout _) (cof_coprod hj hj)
end

end homotopy_theory.cofibrations
