import categories.isomorphism

import .colimits

/-

* Notation and lemmas for categories with `has_coproducts`.

* Construction of pushouts in terms of coproducts and coequalizers.

-/

open set

open categories.category
open categories.isomorphism
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace categories

universes u v

section coproduct
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
(has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.induced f₀ f₁

@[simp] lemma coprod.induced_commutes₀ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₀ = f₀ :=
(has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.induced_commutes₀ f₀ f₁

@[simp] lemma coprod.induced_commutes₁ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₁ = f₁ :=
(has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.induced_commutes₁ f₀ f₁

-- This is a kind of "co-extensionality" lemma; does that count?
@[extensionality] lemma coprod.uniqueness {a₀ a₁ b : C} {k k' : a₀ ⊔ a₁ ⟶ b}
  (e₀ : k ∘ i₀ = k' ∘ i₀) (e₁ : k ∘ i₁ = k' ∘ i₁) : k = k' :=
(has_coproducts.coproduct.{u v} a₀ a₁).is_coproduct.uniqueness e₀ e₁

-- Similarly, this is a "co-eta reduction".
@[simp] lemma coprod.eta {a₀ a₁ b : C} {k : a₀ ⊔ a₁ ⟶ b} :
  coprod.induced (k ∘ i₀) (k ∘ i₁) = k :=
coprod.uniqueness (by simp) (by simp)

def isomorphic_coprod_of_Is_coproduct {a₀ a₁ b : C} {f₀ : a₀ ⟶ b} {f₁ : a₁ ⟶ b}
  (h : Is_coproduct f₀ f₁) : Isomorphism (a₀ ⊔ a₁) b :=
{ morphism := coprod.induced f₀ f₁,
  inverse := h.induced i₀ i₁,
  witness_1 := by apply coprod.uniqueness; { rw ←associativity, simp },
  witness_2 := by apply h.uniqueness; { rw ←associativity, simp } }

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


section uniqueness_of_initial_objects
parameters {C : Type u} [cat : category.{u v} C]
include cat
parameters {a : C} (init : Is_initial_object.{u v} a)
parameters {a' : C} (init' : Is_initial_object.{u v} a')

def initial_object.unique : Isomorphism a a' :=
{ morphism := init.induced,
  inverse := init'.induced,
  witness_1 := init.uniqueness _ _,
  witness_2 := init'.uniqueness _ _ }

end uniqueness_of_initial_objects

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


local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

section isomorphic

parameters {C : Type u} [cat : category.{u v} C]
include cat

-- TODO: Move this somewhere?
def precomposition_bij {a' a x : C} (i : Isomorphism a' a) :
  Bij_on (λ (k : a ⟶ x), (k ∘ ↑i : a' ⟶ x)) univ univ :=
Bij_on.of_equiv $ show (a ⟶ x) ≃ (a' ⟶ x), from
{ to_fun := λ k, k ∘ i.morphism,
  inv_fun := λ k', k' ∘ i.inverse,
  left_inv := λ k, by simp,
  right_inv := λ k', by simp }

parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
parameters {a' b'₀ b'₁ : C} (f'₀ : a' ⟶ b'₀) (f'₁ : a' ⟶ b'₁)
parameters (i : Isomorphism a' a) (j₀ : Isomorphism b'₀ b₀) (j₁ : Isomorphism b'₁ b₁)
parameters (e₀ : f₀ ∘ ↑i = j₀ ∘ f'₀) (e₁ : f₁ ∘ ↑i = j₁ ∘ f'₁)

include e₀ e₁
def Is_pushout_of_isomorphic : Is_pushout f'₀ f'₁ (g₀ ∘ ↑j₀) (g₁ ∘ ↑j₁) :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁}
       : po.universal x
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | (p.1 ∘ ↑j₀) ∘ f'₀ = (p.2 ∘ ↑j₁) ∘ f'₁}
       : begin
           convert Bij_on.refl _, funext p, apply propext,
           rw [←associativity, ←associativity, ←e₀, ←e₁], simp
         end
  ...  ~~ {p : (b'₀ ⟶ x) × (b'₁ ⟶ x) | p.1 ∘ f'₀ = p.2 ∘ f'₁}
       : Bij_on.restrict''
           (Bij_on.prod' (precomposition_bij j₀) (precomposition_bij j₁))
           {p | p.1 ∘ f'₀ = p.2 ∘ f'₁},
  by convert this; funext; simp
omit e₀ e₁

parameters {c' : C} (k : Isomorphism c c')

def Is_pushout_of_isomorphic' : Is_pushout f₀ f₁ ((k : c ⟶ c') ∘ g₀) ((k : c ⟶ c') ∘ g₁) :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ univ
       : precomposition_bij k
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁ }
       : po.universal x,
  by convert this; funext; simp

end isomorphic

section pushout_tranpose

parameters {C : Type u} [cat : category.{u v} C]
include cat
parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)

def Is_pushout.transpose : Is_pushout f₁ f₀ g₁ g₀ :=
Is_pushout.mk $ λ x, calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁}
       : po.universal x
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.2 ∘ f₁ = p.1 ∘ f₀}
       : begin convert Bij_on.refl _; ext p; split; exact eq.symm, end
  ...  ~~ {p' : (b₁ ⟶ x) × (b₀ ⟶ x) | p'.1 ∘ f₁ = p'.2 ∘ f₀}
       : Bij_on.restrict_equiv (equiv.prod_comm _ _)
           {p' | p'.1 ∘ f₁ = p'.2 ∘ f₀}

end pushout_tranpose

section pushout_initial
parameters {C : Type u} [cat : category.{u v} C]
include cat
parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)

def Is_coproduct_of_Is_pushout_of_Is_initial
  (h : Is_initial_object.{u v} a) : Is_coproduct g₀ g₁ :=
have _ := λ x, calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁ }
       : po.universal x
  ...  ~~ (univ : set ((b₀ ⟶ x) × (b₁ ⟶ x)))
       : begin
           convert Bij_on.refl _, symmetry, rw ←univ_subset_iff,
           intros p _, apply h.uniqueness
         end,
Is_coproduct.mk $ λ x, (this x).Is_equiv

end pushout_initial

end categories
