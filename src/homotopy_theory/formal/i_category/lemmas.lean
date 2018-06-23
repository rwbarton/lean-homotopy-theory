import categories.colimit_lemmas
import .definitions

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open categories.has_initial_object categories.preserves_initial_object
open categories.preserves_coproducts
open homotopy_theory.cylinder
open I_category

variables {C : Type u} [category.{u v} C] [has_initial_object.{u v} C]
  [has_coproducts.{u v} C] [Icat : I_category.{u v} C]
include Icat

def Ii_initial : Is_initial_object.{u v} (I +> ∅ : C) :=
Is_initial_object_of_Is_initial_object.{u v} I
  (initial_object.{u v} C).is_initial_object

def I_preserves_coproducts : preserves_coproducts (I : C ↝ C) :=
⟨λ a₀ a₁ b f₀ f₁ copr,
  let po : Is_pushout (! a₀) (! a₁) f₀ f₁ :=
    Is_pushout_of_Is_coproduct_of_Is_initial copr
      (initial_object.{u v} C).is_initial_object in
  Is_coproduct_of_Is_pushout_of_Is_initial
    (I_preserves_pushout_by_cof (all_objects_cofibrant.cofibrant a₀) po) Ii_initial⟩

def I_of_coprod_is_coproduct {a₀ a₁ : C} :
  Is_coproduct (I &> (i₀ : a₀ ⟶ a₀ ⊔ a₁)) (I &> (i₁ : a₁ ⟶ a₀ ⊔ a₁)) :=
let ⟨f⟩ := I_preserves_coproducts in
f (has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct

end homotopy_theory.cofibrations
