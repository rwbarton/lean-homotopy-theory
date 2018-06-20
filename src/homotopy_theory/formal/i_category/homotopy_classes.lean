import categories.congruence
import .homotopy_lemmas

universes u v

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
section
open homotopy_theory.cylinder

parameters {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

def homotopy_congruence ⦃a b : C⦄ := (homotopic : (a ⟶ b) → (a ⟶ b) → Prop)
instance : congruence homotopy_congruence :=
congruence.mk' (λ a b, homotopic_is_equivalence)
  (λ a b c f f' g, homotopic.congr_left g)
  (λ a b c f g g', homotopic.congr_right f)

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

def homotopy_classes_extending_rel : Type v :=
quotient (maps_extending.homotopic_rel hj u)

end
end homotopy_theory.cofibrations
