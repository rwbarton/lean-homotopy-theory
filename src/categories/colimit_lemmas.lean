import categories.isomorphism

import .colimits

/-

* Notation and lemmas for categories with `has_coproducts`.

* Construction of pushouts in terms of coproducts and coequalizers.

-/

open categories.category
open categories.isomorphism
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace categories

universes u v

section coproduct
-- TODO: Write this whole section in terms of Is_coproduct lemmas
variables {C : Type u} [cat : category.{u v} C]
include cat
variable [has_coproducts.{u v} C]

-- The (chosen) coproduct of two objects.
def coprod (a₀ a₁ : C) :=
(has_coproducts.coproduct.{u v} a₀ a₁).ob

notation a₀ ` ⊔ ` a₁ := coprod a₀ a₁

-- The "left" inclusion.
def i₀ {a₀ a₁ : C} : a₀ ⟶ a₀ ⊔ a₁ :=
(has_coproducts.coproduct.{u v} a₀ a₁).map₀

-- The "right" inclusion.
def i₁ {a₀ a₁ : C} : a₁ ⟶ a₀ ⊔ a₁ :=
(has_coproducts.coproduct.{u v} a₀ a₁).map₁

-- The map out of a coproduct induced by a map on each summand.
def coprod.induced {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) : a₀ ⊔ a₁ ⟶ b :=
((has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.universal b).e.inv_fun (f₀, f₁)

@[simp] lemma coprod.induced_commutes₀ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₀ = f₀ :=
congr_arg prod.fst
  ((has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.universal b).cancel_right

@[simp] lemma coprod.induced_commutes₁ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₁ = f₁ :=
congr_arg prod.snd
  ((has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.universal b).cancel_right

-- This is a kind of "co-extensionality" lemma; does that count?
@[extensionality] lemma coprod.uniqueness {a₀ a₁ b : C} {k k' : a₀ ⊔ a₁ ⟶ b}
  (e₀ : k ∘ i₀ = k' ∘ i₀) (e₁ : k ∘ i₁ = k' ∘ i₁) : k = k' :=
((has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.universal b).bijective.1
  (prod.ext.mpr ⟨e₀, e₁⟩)

-- Similarly, this is a "co-eta reduction".
@[simp] lemma coprod.eta {a₀ a₁ b : C} {k : a₀ ⊔ a₁ ⟶ b} :
  coprod.induced (k ∘ i₀) (k ∘ i₁) = k :=
coprod.uniqueness (by simp) (by simp)

end coproduct


section pushouts_from_coequalizers
parameters {C : Type u} [cat : category.{u v} C] [has_coproducts.{u v} C]
include cat

section construction
parameters {a b₀ b₁ b c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}

def Is_pushout_of_Is_coequalizer
  (H : Is_coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁) (coprod.induced g₀ g₁)) :
  Is_pushout f₀ f₁ g₀ g₁ :=
Is_pushout.mk'
  (begin convert H.commutes using 1; rw associativity; simp end)
  (λ x h₀ h₁ e, H.induced (coprod.induced h₀ h₁)
    (begin rw [associativity, associativity], simpa using e end))
  (assume x h₀ h₁ e,
    -- Weird trick to avoid repeating the proof argument
    (λ p, let K := H.induced (coprod.induced h₀ h₁) p in calc
      K ∘ g₀ = K ∘ (coprod.induced g₀ g₁ ∘ i₀)  : by simp
      ...    = (K ∘ coprod.induced g₀ g₁) ∘ i₀  : by rw associativity
      ...    = h₀ : by simp) _)
  (assume x h₀ h₁ e,
    (λ p, let K := H.induced (coprod.induced h₀ h₁) p in calc
      K ∘ g₁ = K ∘ (coprod.induced g₀ g₁ ∘ i₁)  : by simp
      ...    = (K ∘ coprod.induced g₀ g₁) ∘ i₁  : by rw associativity
      ...    = h₁ : by simp) _)
  (assume x k k' e₀ e₁, H.uniqueness $ coprod.uniqueness
    (by rw [←associativity, ←associativity]; simpa using e₀)
    (by rw [←associativity, ←associativity]; simpa using e₁))

def pushout_of_coequalizer (E : coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁)) : pushout f₀ f₁ :=
{ ob := E.ob,
  map₀ := E.map ∘ i₀,
  map₁ := E.map ∘ i₁,
  is_pushout := by
    apply Is_pushout_of_Is_coequalizer; convert E.is_coequalizer; simp }

end construction

def has_pushouts_of_has_coequalizers_and_coproducts [has_coequalizers.{u v} C] :
  has_pushouts.{u v} C :=
{ pushout := λ a b₀ b₁ f₀ f₁,
    pushout_of_coequalizer $ has_coequalizers.coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁) }

end pushouts_from_coequalizers


section uniqueness_of_pushouts

parameters {C : Type u} [cat : category.{u v} C]
include cat
parameters {a b₀ b₁ c c' : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
parameters {g'₀ : b₀ ⟶ c'} {g'₁ : b₁ ⟶ c'} (po' : Is_pushout f₀ f₁ g'₀ g'₁)

@[reducible] private def h : c ⟶ c' := po.induced g'₀ g'₁ po'.commutes
@[reducible] private def h' : c' ⟶ c := po'.induced g₀ g₁ po.commutes

def pushout.unique : Isomorphism c c' :=
{ morphism := h,
  inverse := h',
  witness_1 := by apply po.uniqueness; {rw ←category.associativity, simp},
  witness_2 := by apply po'.uniqueness; {rw ←category.associativity, simp} }

@[simp] lemma pushout.unique_commutes₀ : ↑pushout.unique ∘ g₀ = g'₀ :=
by apply po.induced_commutes₀

@[simp] lemma pushout.unique_commutes₁ : ↑pushout.unique ∘ g₁ = g'₁ :=
by apply po.induced_commutes₁

end uniqueness_of_pushouts

end categories
