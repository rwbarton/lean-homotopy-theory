import .cofibration_category

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open precofibration_category cofibration_category

variables {C : Type u} [cat : category.{v} C] [cofibration_category.{v} C]
include cat

/-

Fibrant objects have the right lifting property with respect to
acyclic cofibrations. Proof: Given f : a → x and an acyclic
cofibration j : a → b, form the pushout square as below; x → y is
again an acyclic cofibration so it admits a retract r : y → x as x is
fibrant. Then b → y → x is a lift of the original map f.

  a → x
  ↓   ↓
  b → y

The converse also holds, by taking a → x to be the identity.

-/

def fibrant_iff_rlp {x : C} :
  fibrant x ↔ ∀ {a b : C} {j : a ⟶ b} (hj : is_acof j) (f : a ⟶ x), ∃ (g : b ⟶ x),
  g ∘ j = f :=
iff.intro
  (assume h a b j hj f, 
    let po := pushout_by_cof j f hj.1,
        ⟨r, hr⟩ := h (pushout_is_acof po.is_pushout hj) in
    ⟨r ∘ po.map₀, by rw [←assoc, po.is_pushout.commutes]; simp [hr]⟩)
  (assume h y j hj, h hj (𝟙 x))

end homotopy_theory.cofibrations
