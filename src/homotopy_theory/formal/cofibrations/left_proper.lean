import .gluing

universes u v

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open precofibration_category cofibration_category
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{u v} C] [cofibration_category.{u v} C]
  [has_initial_object.{u v} C]
include cat

variables {a b a' b' : C} {i : a ⟶ b} {f : a ⟶ a'} {i' : a' ⟶ b'} {f' : b ⟶ b'}
  (po : Is_pushout i f f' i')

lemma pushout_is_weq (ha : cofibrant a) (ha' : cofibrant a') (hi : is_cof i) (hf : is_weq f) :
  is_weq f' :=
have _ := gluing_weq (Is_pushout.refl i) po ha ha ha ha' hi hi
  (weq_id a) (weq_id b) hf (by simp) (by simp),
begin
  convert ←this,
  apply pushout_induced_eq_iff; simp [po.commutes]
end

instance [all_objects_cofibrant.{u v} C] : left_proper.{u v} C :=
{ pushout_weq_by_cof := λ a b a' b' f g f' g' po hf hg,
    by refine pushout_is_weq po _ _ hf hg; exact all_objects_cofibrant.cofibrant _ }

end homotopy_theory.cofibrations
