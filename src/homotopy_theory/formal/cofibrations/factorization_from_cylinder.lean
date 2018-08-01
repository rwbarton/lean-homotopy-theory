import categories.pasting_pushouts
import .cofibration_category

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.weak_equivalences
open homotopy_theory.weak_equivalences.category_with_weak_equivalences
open precofibration_category

/-

If every object of C is cofibrant, then we may replace axiom C3 with
the condition that every object admits a cylinder object, that is, a
cofibration-weak equivalence factorization of the fold map.

-/

variables {C : Type u} [cat : category.{u v} C]
include cat
variables [precofibration_category C] [category_with_weak_equivalences C]
variables [has_initial_object.{u v} C] [all_objects_cofibrant.{u v} C]
variables [has_coproducts.{u v} C]

section mapping_cylinder
variables
  (pushout_is_acof : ∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
    Is_pushout f g g' f' → is_acof f → is_acof f')
  (cylinder : ∀ (a : C), ∃ c (i : a ⊔ a ⟶ c) (p : c ⟶ a),
    is_cof i ∧ is_weq p ∧ p ∘ i = coprod.induced (𝟙 a) (𝟙 a))

variables {a x : C} (f : a ⟶ x)

/-
            f
        a   →   x
      i₁↓  po   ↓
  a → a ⊔ a → a ⊔ x
    i₀ i↓  po'  ↓
        c   →   z

-/

def mapping_cylinder_factorization : ∃ z (j : a ⟶ z) (q : z ⟶ x),
  is_cof j ∧ is_weq q ∧ q ∘ j = f :=
let ⟨c, i, p, hi, hp, pi⟩ := cylinder a,
    po : Is_pushout (i₁ : a ⟶ a ⊔ a) f _ _ := (Is_pushout_i₁ f).transpose,
    po' := pushout_by_cof i (coprod_of_maps (𝟙 a) f) hi,
    po'' :=
      (Is_pushout_of_Is_pushout_of_Is_pushout
        po.transpose po'.is_pushout.transpose).transpose,
    z := po'.ob,
    j := po'.map₁ ∘ i₀,
    q := po''.induced (f ∘ p) (𝟙 x) $ calc
      f ∘ p ∘ (i ∘ i₁)
        = f ∘ ((p ∘ i) ∘ i₁)                     : by simp
    ... = f ∘ (coprod.induced (𝟙 a) (𝟙 a) ∘ i₁)  : by rw pi
    ... = 𝟙 _ ∘ f                                : by simp in
have is_cof j, from
  cof_comp (cof_i₀ (all_objects_cofibrant.cofibrant x)) (pushout_is_cof po'.is_pushout hi),
have is_weq (i ∘ i₁), from
  weq_of_comp_weq_right hp $ by convert (weq_id _); simp [pi],
have is_acof (i ∘ i₁), from
  ⟨cof_comp (cof_i₁ (all_objects_cofibrant.cofibrant a)) hi, this⟩,
have is_acof _, from pushout_is_acof po'' this,
have is_weq q, from
  weq_of_comp_weq_left this.2 $ by convert (weq_id _); simp,
have q ∘ j = f, from calc
  q ∘ j = q ∘ po'.map₁ ∘ (coprod_of_maps (𝟙 a) f ∘ i₀)  : by simp
  ...   = q ∘ (po'.map₁ ∘ coprod_of_maps (𝟙 a) f) ∘ i₀  : by simp only [associativity]
  ...   = q ∘ (po'.map₀ ∘ i) ∘ i₀                : by rw po'.is_pushout.commutes
  ...   = f ∘ ((p ∘ i) ∘ i₀)                     : by simp
  ...   = f ∘ (coprod.induced (𝟙 a) (𝟙 a) ∘ i₀)  : by rw pi
  ...   = f                                      : by simp,
⟨z, j, q, ‹is_cof j›, ‹is_weq q›, this⟩

end mapping_cylinder

def cofibration_category.mk_from_cylinder
  (pushout_is_acof : ∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
    Is_pushout f g g' f' → is_acof f → is_acof f')
  (cylinder : ∀ (a : C), ∃ c (j : a ⊔ a ⟶ c) (g : c ⟶ a),
    is_cof j ∧ is_weq g ∧ g ∘ j = coprod.induced (𝟙 a) (𝟙 a))
  (fibrant_replacement : ∀ (x : C), ∃ rx (j : x ⟶ rx), is_acof j ∧ fibrant rx) :
  cofibration_category.{u v} C :=
{ pushout_is_acof := pushout_is_acof,
  fibrant_replacement := @fibrant_replacement,
  factorization := λ a x f,
    mapping_cylinder_factorization pushout_is_acof cylinder f }

end homotopy_theory.cofibrations
