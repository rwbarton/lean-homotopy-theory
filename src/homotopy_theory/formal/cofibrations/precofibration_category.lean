import category_theory.category
import category_theory.colimits
import category_theory.colimit_lemmas
import category_theory.replete
import category_theory.pasting_pushouts

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations

class has_cofibrations (C : Type u) [category C] :=
(is_cof : Π ⦃a b : C⦄, (a ⟶ b) → Prop)

def is_cof {C : Type u} [category C] [has_cofibrations C] ⦃a b : C⦄ (f : a ⟶ b) : Prop :=
has_cofibrations.is_cof f

/-

We gather here axioms pertaining to cofibrations common to many
notions of "categories with cofibrations".

* The cofibrations form a subcategory which includes all isomorphisms.

* Pushouts of cofibrations exist and are again cofibrations.

An isomorphism is a pushout of an identity map, so it actually
suffices to require that identities are cofibrations.

TODO: In ABC cofibration categories, some of the axioms only apply to
cofibrations with cofibrant domain. Is this sufficient for our
purposes? Useful?

-/

class precofibration_category (C : Type u) [category.{v} C]
  extends has_cofibrations C, wide_subcategory.{v} C is_cof :=
(pushout_by_cof : Π ⦃a b a' : C⦄ (f : a ⟶ b) (g : a ⟶ a'), is_cof f → pushout f g)
(pushout_is_cof : ∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
  Is_pushout f g g' f' → is_cof f → is_cof f')

open precofibration_category

variables {C : Type u} [cat : category.{v} C] [precofibration_category C]
include cat
lemma cof_id (a : C) : is_cof (𝟙 a) := mem_id a
lemma cof_comp {a b c : C} {f : a ⟶ b} {g : b ⟶ c} :
  is_cof f → is_cof g → is_cof (g ∘ f) := mem_comp
omit cat

instance precofibration_category.replete
  (C : Type u) [category.{v} C] [p : precofibration_category.{v} C] :
  replete_wide_subcategory.{v} C is_cof :=
{ mem_iso := assume a b i,
    pushout_is_cof
      (by convert Is_pushout_of_isomorphic' (Is_pushout.refl (𝟙 a)) i; simp; refl)
      (cof_id a) }

include cat
lemma cof_iso {a b : C} (i : a ≅ b) : is_cof i.hom := mem_iso i

-- The coproduct of cofibrations is a cofibration.
-- TODO: Should we try to express this using Is_coproduct?
-- TODO: Make `coproduct` a class and use it in notation
lemma cof_coprod [has_initial_object.{v} C] [has_coproducts.{v} C]
  {a₀ b₀ a₁ b₁ : C} {j₀ : a₀ ⟶ b₀} {j₁ : a₁ ⟶ b₁} (h₀ : is_cof j₀) (h₁ : is_cof j₁) :
  is_cof (coprod_of_maps j₀ j₁) :=
begin
  convert cof_comp
    (pushout_is_cof (Is_pushout_i₀ j₀) h₀)
    (pushout_is_cof (Is_pushout_i₁ j₁) h₁),
  apply coprod.uniqueness; { rw ←assoc, simp }
end

-- Basically the same as above, but in the slice category a/C and for
-- arbitrary (rather than chosen) pushouts.
lemma cof_pushout {a b₀ b₁ c b₀' b₁' c' : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
  {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} {g₀' : b₀' ⟶ c'} {g₁' : b₁' ⟶ c'}
  {h₀ : b₀ ⟶ b₀'} {h₁ : b₁ ⟶ b₁'} (hh₀ : is_cof h₀) (hh₁ : is_cof h₁)
  (po : Is_pushout f₀ f₁ g₀ g₁) (po' : Is_pushout (h₀ ∘ f₀) (h₁ ∘ f₁) g₀' g₁') (e) :
  is_cof (po.induced (g₀' ∘ h₀) (g₁' ∘ h₁) e) :=
let po₀ := pushout_by_cof h₀ g₀ hh₀,
    po₁ := Is_pushout_of_Is_pushout_of_Is_pushout_vert po po₀.is_pushout,
    k₁ := po₁.induced g₀' (g₁' ∘ h₁) (by simpa using e) in
have k₁ ∘ po₀.map₀ = g₀', by simp,
let po₂ := Is_pushout_of_Is_pushout_of_Is_pushout' po₁ (by convert po') (by simp) in
have k₁ ∘ po₀.map₁ = po.induced (g₀' ∘ h₀) (g₁' ∘ h₁) e, begin
  apply po.uniqueness,
  { rw [←assoc, ←po₀.is_pushout.commutes], simp },
  { rw [←assoc, po₂.commutes], simp }
end,
by rw ←this;
   exact cof_comp (pushout_is_cof po₀.is_pushout hh₀) (pushout_is_cof po₂.transpose hh₁)

-- Suppose C has an initial object ∅. Then an object A of C is
-- cofibrant if the unique map ∅ → A is a cofibration.
variables [has_initial_object.{v} C]

def cofibrant (a : C) : Prop := is_cof (! a)

-- TODO: Apply this in many places
lemma cofibrant_of_cof {a b : C} {j : a ⟶ b} (ha : cofibrant a) (hj : is_cof j) :
  cofibrant b :=
begin
  change is_cof _,
  convert cof_comp ha hj,
  apply initial.uniqueness
end

lemma cofibrant_coprod [has_initial_object.{v} C] [has_coproducts.{v} C]
  {a₀ a₁ : C} (h₀ : cofibrant a₀) (h₁ : cofibrant a₁) : cofibrant (a₀ ⊔ a₁) :=
begin
  change is_cof (! _),
  convert cof_comp (cof_iso (coprod_initial_left ∅)) (cof_coprod h₀ h₁),
  apply initial.uniqueness
end

lemma cof_i₀ [has_initial_object.{v} C] [has_coproducts.{v} C]
  {a₀ a₁ : C} (h : cofibrant a₁) : is_cof (i₀ : a₀ ⟶ a₀ ⊔ a₁) :=
by convert cof_comp (cof_iso (coprod_initial_right a₀)) (cof_coprod (cof_id a₀) h);
   simp

lemma cof_i₁ [has_initial_object.{v} C] [has_coproducts.{v} C]
  {a₀ a₁ : C} (h : cofibrant a₀) : is_cof (i₁ : a₁ ⟶ a₀ ⊔ a₁) :=
by convert cof_comp (cof_iso (coprod_initial_left a₁)) (cof_coprod h (cof_id a₁));
   simp

variables (C)
class all_objects_cofibrant [has_initial_object.{v} C] :=
(cofibrant : ∀ (a : C), cofibrant a)

end homotopy_theory.cofibrations
