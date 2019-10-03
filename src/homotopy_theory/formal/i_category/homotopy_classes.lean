import category_theory.congruence
import .homotopy_lemmas

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
section C
parameters {C : Type u} [cat : category.{v} C]
  [has_initial_object.{v} C] [has_coproducts.{v} C] [I_category.{v} C]
include cat

section
open homotopy_theory.cylinder

def homotopy_congruence ⦃a b : C⦄ := (homotopic : (a ⟶ b) → (a ⟶ b) → Prop)
instance : congruence homotopy_congruence :=
congruence.mk' (λ a b, homotopic_is_equivalence)
  (λ a b c f f' g, homotopic.congr_left g)
  (λ a b c f g g', homotopic.congr_right f)

@[reducible] def homotopy_classes (a b : C) : Type v :=
@has_hom.hom (category_mod_congruence C homotopy_congruence) _ a b

variables {a b : C} {j : a ⟶ b} (hj : is_cof j) {x : C} (u : a ⟶ x)
include hj

def maps_extending : Type v := {v : b ⟶ x // v ∘ j = u}
instance maps_extending.homotopic_rel : setoid (maps_extending hj u) :=
{ r := λ f g, homotopic_rel j f.val g.val,
  -- TODO: preimage of an equivalence relation is an equivalence relation
  iseqv :=
    ⟨λ f, homotopic_rel.refl f.val,
     λ f g, homotopic_rel.symm hj,
     λ f g h, homotopic_rel.trans hj⟩ }

variables (j)
def homotopy_classes_extending_rel : Type v :=
quotient (maps_extending.homotopic_rel hj u)

variables {y : C} (g : x ⟶ y) {j hj u}

-- TODO: naming
def hcer_induced : homotopy_classes_extending_rel j hj u → homotopy_classes_extending_rel j hj (g ∘ u) :=
λ f, quotient.lift_on f
  (λ f, (⟦⟨g ∘ f.val, by rw [←assoc, f.property]⟩⟧ : homotopy_classes_extending_rel j hj (g ∘ u)))
  (assume f f' H, quotient.sound (H.congr_left g))
end

end C
end homotopy_theory.cofibrations
