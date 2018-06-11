import categories.colimits
import categories.isomorphism
import categories.replete
import .definitions

open categories
open categories.category
open categories.isomorphism
local notation f ` ∘ `:80 g:80 := g ≫ f

universes u v

namespace homotopy_theory.cylinder

section hep

variables {C : Type u} [category.{u v} C] [inst1 : has_cylinder C] [inst2 : has_cylinder_with_involution C]

include inst1

-- The homotopy extension property with respect to the given cylinder
-- functor, "on side ε".
def hep (ε) {A X : C} (j : A ⟶ X) : Prop :=
∀ Y (f : X ⟶ Y) (H : I +> A ⟶ Y), f ∘ j = H ∘ i ε @> A →
  ∃ H' : I +> X ⟶ Y, H' ∘ i ε @> X = f ∧ H' ∘ I &> j = H

lemma hep_of_isomorphism (ε) {A X : C} (h : Isomorphism A X) : hep ε h.morphism :=
assume Y f H e,
  ⟨H ∘ I &> h.inverse,
   by erw [←associativity, ←(i ε).naturality, associativity, ←e, Isomorphism.witness_2_assoc_lemma],
   by erw [←functor.Functor.onIsomorphisms.inverse, Isomorphism.witness_1_assoc_lemma]⟩

lemma hep_id (ε) {X : C} : hep ε (𝟙 X) :=
hep_of_isomorphism ε (Isomorphism.refl X)

lemma hep_comp (ε) {A B X : C} {f : A ⟶ B} {g : B ⟶ X} (hf : hep ε f) (hg : hep ε g) :
  hep ε (g ∘ f) :=
assume Y k H e,
  let ⟨J, Je₁, Je₂⟩ := hf Y (k ∘ g) H (by convert e using 1; simp) in
  let ⟨K, Ke₁, Ke₂⟩ := hg Y k J Je₁.symm in
  ⟨K, Ke₁, by rw [I.functoriality, associativity, Ke₂, Je₂]⟩

instance hep_replete (ε) : replete_wide_subcategory.{u v} C (λ a b, hep ε) :=
replete_wide_subcategory.mk' (λ a b, hep_of_isomorphism ε) (λ a b c f g, hep_comp ε)

lemma hep_iff_pushout_retract (ε) {A X : C} {j : A ⟶ X}
  {Z : C} {i' : X ⟶ Z} {j' : I +> A ⟶ Z} (po : Is_pushout j (i ε @> A) i' j') :
  hep ε j ↔ ∃ r : I +> X ⟶ Z,
    r ∘ po.induced (i ε @> X) (I &> j) ((i ε).naturality _) = 𝟙 _ :=
iff.intro
  (assume h,
    let ⟨r, hr₁, hr₂⟩ := h Z i' j' po.commutes in
    ⟨r, by apply po.uniqueness; rw ←associativity; simpa⟩)
  (assume ⟨r, hr⟩ Y f H e,
    have hr₁ : r ∘ i ε @> X = i', from eq.symm $ calc
      i' = 𝟙 _ ∘ i' : by simp
     ... = (r ∘ _) ∘ i' : by rw hr
     ... = _ : by rw ←associativity; simp,
    have hr₂ : r ∘ I &> j = j', from eq.symm $ calc
      j' = 𝟙 _ ∘ j' : by simp
     ... = (r ∘ _) ∘ j' : by rw hr
     ... = _ : by rw ←associativity; simp,
    ⟨po.induced f H e ∘ r,
     by rw [←associativity, hr₁]; simp,
     by rw [←associativity, hr₂]; simp⟩)

-- The two-sided homotopy extension property.
@[reducible] def two_sided_hep {A X : C} (j : A ⟶ X) : Prop := ∀ ε, hep ε j

omit inst1
include inst2

lemma hep_involution {ε} {A X : C} {j : A ⟶ X} (h : hep ε j) : hep ε.v j :=
assume Y f H e,
  let ⟨H₁, h₁, h₂⟩ := h Y f (H ∘ v @> A)
    (by convert e using 1; rw [←associativity]; simp) in
  ⟨H₁ ∘ v @> X,
   by rw ←associativity; simpa,
   calc
     H₁ ∘ v @> X ∘ I &> j
       = H₁ ∘ (v @> X ∘ I &> j) : by simp
   ... = H₁ ∘ (I &> j ∘ v @> A) : by rw v.naturality
   ... = (H₁ ∘ I &> j) ∘ v @> A : by simp
   ... = (H ∘ v @> A) ∘ v @> A  : by rw h₂
   ... = H                      : by rw ←associativity; simp⟩

lemma two_sided_hep_iff_hep {ε} {A X : C} {j : A ⟶ X} : two_sided_hep j ↔ hep ε j :=
have ∀ ε', ε' = ε ∨ ε' = ε.v, by intro ε'; cases ε; cases ε'; simp; refl,
iff.intro (assume h, h ε)
  (assume h ε', begin
    cases this ε'; subst ε', { exact h }, { exact hep_involution h }
  end)

end hep

end homotopy_theory.cylinder
