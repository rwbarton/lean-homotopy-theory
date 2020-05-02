import homotopy_theory.formal.weak_equivalences.definitions
import .precofibration_category

universes v u

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.weak_equivalences

variables {C : Type u} [category.{v} C]

/-

[Baues, Algebraic homotopy, §I.1] defines a cofibration category to be
a category equipped with cofibrations and weak equivalences satisfying
the following axioms.

C1. Weak equivalences and cofibrations are subcategories which contain
    all the isomorphisms, and weak equivalences satisfy two-out-of-three.

C2. Pushouts by cofibrations exist and are again cofibrations. Moreover,
    (a) a pushout of a weak equivalence by a cofibration is again a weak
        equivalence;
    (b) a pushout of an acyclic cofibration is again acyclic.

C3. Any map may be factored into a cofibration followed by a weak
    equivalence.

C4. For any object X, there exists an acyclic cofibration X → RX with
    RX fibrant, that is, any trivial cofibration out of RX admits a
    retract.

We omit the axiom C2(a). As Baues already notes, many results on
cofibration categories do not depend on this axiom. We call a
cofibration category which additionally satisfies C2(a) left proper.

Axiom C1 and the first part of axiom C2 are contained in the
superclasses `category_with_weak_equivalences`,
`precofibration_category`. The remaining axioms are C2(b), C3, C4.

-/

def is_acof [precofibration_category C] [category_with_weak_equivalences C]
  {a x : C} (j : a ⟶ x) : Prop := is_cof j ∧ is_weq j

def fibrant [precofibration_category C] [category_with_weak_equivalences C]
  (x : C) : Prop :=
∀ ⦃y⦄ {j : x ⟶ y} (hj : is_acof j), ∃ r, r ∘ j = 𝟙 x

variables (C)
class cofibration_category extends category_with_weak_equivalences C,
  precofibration_category.{v} C :=
(pushout_is_acof : ∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
  Is_pushout f g g' f' → is_acof f → is_acof f')
(factorization : ∀ {a x : C} (f : a ⟶ x), ∃ b (j : a ⟶ b) (g : b ⟶ x),
  is_cof j ∧ is_weq g ∧ g ∘ j = f)
(fibrant_replacement : ∀ (x : C), ∃ rx (j : x ⟶ rx), is_acof j ∧ fibrant rx)

-- Baues' axiom C2(a).
class left_proper [cofibration_category.{v} C] : Prop :=
(pushout_weq_by_cof : ∀ ⦃a b a' b' : C⦄ {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
  Is_pushout f g g' f' → is_cof f → is_weq g → is_weq g')

end homotopy_theory.cofibrations
