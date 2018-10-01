import category_theory.colimits
import category_theory.isomorphism
import category_theory.iso_lemmas
import category_theory.preserves_colimits
import category_theory.replete
import .definitions
import category_theory.functor

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

universes u v

namespace homotopy_theory.cylinder

section hep

variables {C : Type u} [category.{u v} C] [inst1 : has_cylinder C] [inst2 : has_cylinder_with_involution C]

include inst1

-- The homotopy extension property with respect to the given cylinder
-- functor, "on side ε".
def hep (ε) {A X : C} (j : A ⟶ X) : Prop :=
∀ Y (f : X ⟶ Y) (H : I.obj A ⟶ Y), f ∘ j = H ∘ i ε @> A →
  ∃ H' : I.obj X ⟶ Y, H' ∘ i ε @> X = f ∧ H' ∘ I &> j = H

lemma hep_of_isomorphism (ε) {A X : C} (h : iso A X) : hep ε (h : A ⟶ X) :=
assume Y f H e,
  ⟨H ∘ I &> h.inv,
   by erw [←assoc, ←(i ε).naturality, assoc, ←e, iso.inv_hom_id_assoc_lemma],
   by erw [←functor.on_iso_hom, iso.hom_inv_id_assoc_lemma]⟩

lemma hep_id (ε) {X : C} : hep ε (𝟙 X) :=
hep_of_isomorphism ε (iso.refl X)

lemma hep_comp (ε) {A B X : C} {f : A ⟶ B} {g : B ⟶ X} (hf : hep ε f) (hg : hep ε g) :
  hep ε (g ∘ f) :=
assume Y k H e,
  let ⟨J, Je₁, Je₂⟩ := hf Y (k ∘ g) H (by convert e using 1; simp) in
  let ⟨K, Ke₁, Ke₂⟩ := hg Y k J Je₁.symm in
  ⟨K, Ke₁, by rw [I.map_comp, assoc, Ke₂, Je₂]⟩

instance hep_replete (ε) : replete_wide_subcategory.{u v} C (λ a b, hep ε) :=
replete_wide_subcategory.mk' (λ a b, hep_of_isomorphism ε) (λ a b c f g, hep_comp ε)

lemma hep_pushout (ε) {A B A' B' : C} {f : A ⟶ B} {g : A ⟶ A'} {f' : A' ⟶ B'} {g' : B ⟶ B'}
  (po : Is_pushout f g g' f') (po' : Is_pushout (I &> f) (I &> g) (I &> g') (I &> f'))
  (hf : hep ε f) : hep ε f' :=
assume Y h H e,
  have (h ∘ g') ∘ f = (H ∘ (I &> g)) ∘ i ε @> A, begin
    erw [←assoc, ←assoc, po.commutes, ←(i ε).naturality],
    simp [e]
  end,
  let ⟨J, Je₁, Je₂⟩ := hf Y (h ∘ g') (H ∘ (I &> g)) this in
  let K := po'.induced J H Je₂ in
  ⟨K,
   begin
     apply po.uniqueness; erw [←assoc, (i ε).naturality, assoc],
     { rw [←Je₁], simp },
     { rw [e], simp }
   end,
   po'.induced_commutes₁ J H Je₂⟩

lemma hep_pushout' [preserves_pushouts (I : C ↝ C)] (ε) {A B A' B' : C}
  {f : A ⟶ B} {g : A ⟶ A'} {f' : A' ⟶ B'} {g' : B ⟶ B'} (po : Is_pushout f g g' f')
  (hf : hep ε f) : hep ε f' :=
hep_pushout ε po (preserves_pushouts.Is_pushout_of_Is_pushout I po) hf

lemma hep_iff_pushout_retract (ε) {A X : C} {j : A ⟶ X}
  {Z : C} {i' : X ⟶ Z} {j' : I.obj A ⟶ Z} (po : Is_pushout j (i ε @> A) i' j') :
  hep ε j ↔ ∃ r : I.obj X ⟶ Z,
    r ∘ po.induced (i ε @> X) (I &> j) ((i ε).naturality _) = 𝟙 _ :=
iff.intro
  (assume h,
    let ⟨r, hr₁, hr₂⟩ := h Z i' j' po.commutes in
    ⟨r, by apply po.uniqueness; rw ←assoc; simpa⟩)
  (assume ⟨r, hr⟩ Y f H e,
    have hr₁ : r ∘ i ε @> X = i', from eq.symm $ calc
      i' = 𝟙 _ ∘ i' : by simp
     ... = (r ∘ _) ∘ i' : by rw hr
     ... = _ : by rw ←assoc; simp,
    have hr₂ : r ∘ I &> j = j', from eq.symm $ calc
      j' = 𝟙 _ ∘ j' : by simp
     ... = (r ∘ _) ∘ j' : by rw hr
     ... = _ : by rw ←assoc; simp,
    ⟨po.induced f H e ∘ r,
     by rw [←assoc, hr₁]; simp,
     by rw [←assoc, hr₂]; simp⟩)

lemma hep_initial_induced (ε) {A X : C} {j : A ⟶ X}
  (Ai : Is_initial_object.{u v} A) (IAi : Is_initial_object.{u v} (I.obj A)) :
  hep ε j :=
let po : Is_pushout j (i ε @> A) (𝟙 X) IAi.induced := begin
  convert Is_pushout_of_isomorphic (Is_pushout.refl j) j (i ε @> A)
    (iso.refl A) (iso.refl X) (initial_object.unique IAi Ai)
    (Ai.uniqueness _ _) (Ai.uniqueness _ _), { simp }, { apply IAi.uniqueness }
end in
(hep_iff_pushout_retract ε po).mpr ⟨p @> X, po.uniqueness
  (by rw [←assoc, po.induced_commutes₀]; simp)
  (IAi.uniqueness _ _)⟩

-- The two-sided homotopy extension property.
@[reducible] def two_sided_hep {A X : C} (j : A ⟶ X) : Prop := ∀ ε, hep ε j

omit inst1
include inst2

lemma hep_involution {ε} {A X : C} {j : A ⟶ X} (h : hep ε j) : hep ε.v j :=
assume Y f H e,
  let ⟨H₁, h₁, h₂⟩ := h Y f (H ∘ v @> A)
    (by convert e using 1; rw [←assoc]; simp) in
  ⟨H₁ ∘ v @> X,
   by rw ←assoc; simp; rw endpoint.vv; simpa using H₁,
   calc
     H₁ ∘ v @> X ∘ I &> j
       = H₁ ∘ (v @> X ∘ I &> j) : by simp
   ... = H₁ ∘ (I &> j ∘ v @> A) : by erw v.naturality; refl
   ... = (H₁ ∘ I &> j) ∘ v @> A : by simp
   ... = (H ∘ v @> A) ∘ v @> A  : by rw h₂
   ... = H                      : by rw ←assoc; simp; dsimp; simp⟩

lemma two_sided_hep_iff_hep {ε} {A X : C} {j : A ⟶ X} : two_sided_hep j ↔ hep ε j :=
have ∀ ε', ε' = ε ∨ ε' = ε.v, by intro ε'; cases ε; cases ε'; simp; refl,
iff.intro (assume h, h ε)
  (assume h ε', begin
    cases this ε'; subst ε', { exact h }, { exact hep_involution h }
  end)

end hep

end homotopy_theory.cylinder
