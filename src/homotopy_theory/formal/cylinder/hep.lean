import .definitions

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.cylinder

section hep

variables {C : Type u} [category C] [inst1 : has_cylinder C] [inst2 : has_cylinder_with_involution C]

include inst1

-- The homotopy extension property with respect to the given cylinder
-- functor, "on side ε".
def hep (ε) {A X : C} (j : A ⟶ X) : Prop :=
∀ Y (f : X ⟶ Y) (H : I +> A ⟶ Y), f ∘ j = H ∘ i ε @> A →
  ∃ H' : I +> X ⟶ Y, f = H' ∘ i ε @> X ∧ H' ∘ I &> j = H

-- The two-sided homotopy extension property.
@[reducible] def two_sided_hep {A X : C} (j : A ⟶ X) : Prop := ∀ ε, hep ε j

omit inst1
include inst2

lemma hep_involution {ε} {A X : C} {j : A ⟶ X} (h : hep ε j) : hep ε.v j :=
assume Y f H e,
  let ⟨H₁, h₁, h₂⟩ := h Y f (H ∘ v @> A)
    (by convert e using 1; rw [←associativity]; simp) in
  ⟨H₁ ∘ v @> X,
   by rw [h₁, ←associativity]; congr; simp,
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
