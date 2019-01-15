import category_theory.isomorphism

import .colimits

/-

* Notation and lemmas for categories with `has_coproducts`.

* Construction of pushouts in terms of coproducts and coequalizers.

-/

open set

open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace category_theory

universes v u

section initial
variables {C : Type u} [cat : category.{v} C]
include cat
variable [has_initial_object.{v} C]

def initial : C := (has_initial_object.initial_object.{v} C).ob

instance : has_emptyc C := ⟨initial⟩

def initial.induced (a : C) : ∅ ⟶ a :=
(has_initial_object.initial_object.{v} C).is_initial_object.induced

notation `!` a := initial.induced a

def initial.uniqueness {a : C} (k k' : ∅ ⟶ a) : k = k' :=
(has_initial_object.initial_object.{v} C).is_initial_object.uniqueness k k'

-- This instance tends not to be very useful because `congr` generates
-- a congruence lemma which is too general, and does not "know" that
-- the domain is ∅.
instance (a : C) : subsingleton (∅ ⟶ a) := ⟨initial.uniqueness⟩

end initial

section coproduct
variables {C : Type u} [cat : category.{v} C]
include cat
variable [has_coproducts.{v} C]

-- The (chosen) coproduct of two objects.
def coprod (a₀ a₁ : C) :=
(has_coproducts.coproduct.{v} a₀ a₁).ob

notation a₀ ` ⊔ ` a₁ := coprod a₀ a₁

-- The "left" inclusion.
def i₀ {a₀ a₁ : C} : a₀ ⟶ a₀ ⊔ a₁ :=
(has_coproducts.coproduct.{v} a₀ a₁).map₀

-- The "right" inclusion.
def i₁ {a₀ a₁ : C} : a₁ ⟶ a₀ ⊔ a₁ :=
(has_coproducts.coproduct.{v} a₀ a₁).map₁

-- The map out of a coproduct induced by a map on each summand.
def coprod.induced {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) : a₀ ⊔ a₁ ⟶ b :=
(has_coproducts.coproduct.{v} a₀ a₁).is_coproduct.induced f₀ f₁

def coprod.induced_Is_equiv {a₀ a₁ b : C} :
  Is_equiv (λ p : (a₀ ⟶ b) × (a₁ ⟶ b), coprod.induced p.1 p.2) :=
{ e := ((has_coproducts.coproduct a₀ a₁).is_coproduct.universal b).e.symm,
  h := by funext p; cases p; refl }

@[simp] lemma coprod.induced_commutes₀ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₀ = f₀ :=
(has_coproducts.coproduct.{v} a₀ a₁).is_coproduct.induced_commutes₀ f₀ f₁

@[simp] lemma coprod.induced_commutes₁ {a₀ a₁ b : C} (f₀ : a₀ ⟶ b) (f₁ : a₁ ⟶ b) :
  coprod.induced f₀ f₁ ∘ i₁ = f₁ :=
(has_coproducts.coproduct.{v} a₀ a₁).is_coproduct.induced_commutes₁ f₀ f₁

def coprod.fold (a : C) : a ⊔ a ⟶ a :=
coprod.induced (𝟙 a) (𝟙 a)

@[simp] lemma coprod.fold_i₀ {a : C} : coprod.fold a ∘ i₀ = 𝟙 a :=
coprod.induced_commutes₀ _ _

@[simp] lemma coprod.fold_i₁ {a : C} : coprod.fold a ∘ i₁ = 𝟙 a :=
coprod.induced_commutes₁ _ _

-- This is a kind of "co-extensionality" lemma; does that count?
@[extensionality] lemma coprod.uniqueness {a₀ a₁ b : C} {k k' : a₀ ⊔ a₁ ⟶ b}
  (e₀ : k ∘ i₀ = k' ∘ i₀) (e₁ : k ∘ i₁ = k' ∘ i₁) : k = k' :=
(has_coproducts.coproduct.{v} a₀ a₁).is_coproduct.uniqueness e₀ e₁

lemma coprod.ext {a₀ a₁ b : C} {k k' : a₀ ⊔ a₁ ⟶ b} :
  k = k' ↔ k ∘ i₀ = k' ∘ i₀ ∧ k ∘ i₁ = k' ∘ i₁ :=
iff.intro (assume h, by rw h; simp) (assume ⟨h₀, h₁⟩, coprod.uniqueness h₀ h₁)

-- Similarly, this is a "co-eta reduction".
@[simp] lemma coprod.eta {a₀ a₁ b : C} {k : a₀ ⊔ a₁ ⟶ b} :
  coprod.induced (k ∘ i₀) (k ∘ i₁) = k :=
coprod.uniqueness (by simp) (by simp)

def coprod_of_maps {a₀ a₁ b₀ b₁ : C} (f₀ : a₀ ⟶ b₀) (f₁ : a₁ ⟶ b₁) : a₀ ⊔ a₁ ⟶ b₀ ⊔ b₁ :=
coprod.induced (i₀ ∘ f₀) (i₁ ∘ f₁)

@[simp] lemma coprod_of_maps_commutes₀ {a₀ a₁ b₀ b₁ : C} {f₀ : a₀ ⟶ b₀} {f₁ : a₁ ⟶ b₁} :
  coprod_of_maps f₀ f₁ ∘ i₀ = i₀ ∘ f₀ :=
coprod.induced_commutes₀ _ _

@[simp] lemma coprod_of_maps_commutes₁ {a₀ a₁ b₀ b₁ : C} {f₀ : a₀ ⟶ b₀} {f₁ : a₁ ⟶ b₁} :
  coprod_of_maps f₀ f₁ ∘ i₁ = i₁ ∘ f₁ :=
coprod.induced_commutes₁ _ _

def isomorphic_coprod_of_Is_coproduct {a₀ a₁ b : C} {f₀ : a₀ ⟶ b} {f₁ : a₁ ⟶ b}
  (h : Is_coproduct f₀ f₁) : iso (a₀ ⊔ a₁) b :=
{ hom := coprod.induced f₀ f₁,
  inv := h.induced i₀ i₁,
  hom_inv_id' := by apply coprod.uniqueness; { rw ←assoc, simp },
  inv_hom_id' := by apply h.uniqueness; { rw ←assoc, simp } }

def coprod_of_isomorphisms {a₀ a₁ b₀ b₁ : C} (j₀ : iso a₀ b₀) (j₁ : iso a₁ b₁) :
  iso (a₀ ⊔ a₁) (b₀ ⊔ b₁) :=
{ hom := coprod_of_maps j₀.hom j₁.hom,
  inv := coprod_of_maps j₀.inv j₁.inv,
  hom_inv_id' := by apply coprod.uniqueness; rw ←assoc; simp,
  inv_hom_id' := by apply coprod.uniqueness; rw ←assoc; simp }

variables [has_initial_object.{v} C]

def coprod_initial_right (a : C) : a ≅ a ⊔ ∅ :=
{ hom := i₀,
  inv := coprod.induced (𝟙 a) (! a),
  hom_inv_id' := by simp,
  inv_hom_id' :=
    by apply coprod.uniqueness; try { apply initial.uniqueness };
       rw ←assoc; simp }

@[simp] lemma coprod_initial_right_hom {a : C} : (coprod_initial_right a).hom = i₀ :=
rfl

def coprod_initial_left (a : C) : a ≅ ∅ ⊔ a :=
{ hom := i₁,
  inv := coprod.induced (! a) (𝟙 a),
  hom_inv_id' := by simp,
  inv_hom_id' :=
    by apply coprod.uniqueness; try { apply initial.uniqueness };
       rw ←assoc; simp }

@[simp] lemma coprod_initial_left_hom {a : C} : (coprod_initial_left a).hom = i₁ :=
rfl

end coproduct


section pushout_induced_eq
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b₀ b₁ c c' : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)

lemma pushout_induced_eq_iff {x : C} {h₀ : b₀ ⟶ x} {h₁ : b₁ ⟶ x} {k : c ⟶ x} {e}
  (H₀ : h₀ = g₀ ≫ k) (H₁ : h₁ = g₁ ≫ k) : po.induced h₀ h₁ e = k :=
by apply po.uniqueness; simp [H₀, H₁]

end pushout_induced_eq


section pushout_induced_comp
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b₀ b₁ c c' : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)

lemma pushout_induced_comp {x y : C} {h₀ : b₀ ⟶ x} {h₁ : b₁ ⟶ x} {k : x ⟶ y} {e} :
  k ∘ po.induced h₀ h₁ e = po.induced (k ∘ h₀) (k ∘ h₁)
    (by rw [←assoc, ←assoc, e]) :=
by apply po.uniqueness; rw ←assoc; simp

end pushout_induced_comp

section pushouts_from_coequalizers
parameters {C : Type u} [cat : category.{v} C] [has_coproducts.{v} C]
include cat

section construction
parameters {a b₀ b₁ b c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}

def Is_pushout_of_Is_coequalizer
  (H : Is_coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁) (coprod.induced g₀ g₁)) :
  Is_pushout f₀ f₁ g₀ g₁ :=
Is_pushout.mk'
  (begin convert H.commutes using 1; rw assoc; simp end)
  (λ x h₀ h₁ e, H.induced (coprod.induced h₀ h₁)
    (begin rw [assoc, assoc], simpa using e end))
  (assume x h₀ h₁ e,
    -- Weird trick to avoid repeating the proof argument
    (λ p, let K := H.induced (coprod.induced h₀ h₁) p in calc
      K ∘ g₀ = K ∘ (coprod.induced g₀ g₁ ∘ i₀)  : by simp
      ...    = (K ∘ coprod.induced g₀ g₁) ∘ i₀  : by rw assoc
      ...    = h₀ : by simp) _)
  (assume x h₀ h₁ e,
    (λ p, let K := H.induced (coprod.induced h₀ h₁) p in calc
      K ∘ g₁ = K ∘ (coprod.induced g₀ g₁ ∘ i₁)  : by simp
      ...    = (K ∘ coprod.induced g₀ g₁) ∘ i₁  : by rw assoc
      ...    = h₁ : by simp) _)
  (assume x k k' e₀ e₁, H.uniqueness $ coprod.uniqueness
    (by rw [←assoc, ←assoc]; simpa using e₀)
    (by rw [←assoc, ←assoc]; simpa using e₁))

def pushout_of_coequalizer (E : coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁)) : pushout f₀ f₁ :=
{ ob := E.ob,
  map₀ := E.map ∘ i₀,
  map₁ := E.map ∘ i₁,
  is_pushout := by
    apply Is_pushout_of_Is_coequalizer; convert E.is_coequalizer; simp }

end construction

def has_pushouts_of_has_coequalizers_and_coproducts [has_coequalizers.{v} C] :
  has_pushouts.{v} C :=
{ pushout := λ a b₀ b₁ f₀ f₁,
    pushout_of_coequalizer $ has_coequalizers.coequalizer (i₀ ∘ f₀) (i₁ ∘ f₁) }

end pushouts_from_coequalizers


section uniqueness_of_initial_objects
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a : C} (init : Is_initial_object.{v} a)
parameters {a' : C} (init' : Is_initial_object.{v} a')

def initial_object.unique : iso a a' :=
{ hom := init.induced,
  inv := init'.induced,
  hom_inv_id' := init.uniqueness _ _,
  inv_hom_id' := init'.uniqueness _ _ }

end uniqueness_of_initial_objects

section uniqueness_of_pushouts

parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b₀ b₁ c c' : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
parameters {g'₀ : b₀ ⟶ c'} {g'₁ : b₁ ⟶ c'} (po' : Is_pushout f₀ f₁ g'₀ g'₁)

@[reducible] private def h : c ⟶ c' := po.induced g'₀ g'₁ po'.commutes
@[reducible] private def h' : c' ⟶ c := po'.induced g₀ g₁ po.commutes

def pushout.unique : iso c c' :=
{ hom := h,
  inv := h',
  hom_inv_id' := by apply po.uniqueness; {rw ←category.assoc, simp},
  inv_hom_id' := by apply po'.uniqueness; {rw ←category.assoc, simp} }

@[simp] lemma pushout.unique_commutes₀ : pushout.unique.hom ∘ g₀ = g'₀ :=
by apply po.induced_commutes₀

@[simp] lemma pushout.unique_commutes₁ : pushout.unique.hom ∘ g₁ = g'₁ :=
by apply po.induced_commutes₁

end uniqueness_of_pushouts


local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

section refl
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b : C} (f : a ⟶ b)

def Is_pushout.refl : Is_pushout f (𝟙 a) (𝟙 b) f :=
Is_pushout.mk $ λ x,
  Bij_on.mk
    { to_fun := λ h, ⟨(h ∘ 𝟙 b, h ∘ f), by simp⟩,
      inv_fun := λ p, ⟨p.val.1, trivial⟩,
      left_inv := assume h, by simp,
      right_inv := assume ⟨⟨pv1, pv2⟩, pp⟩, by simpa using pp }
    (assume h, rfl)

end refl

section isomorphic

parameters {C : Type u} [cat : category.{v} C]
include cat

-- TODO: Move this somewhere?
def precomposition_bij {a' a x : C} (i : iso a' a) :
  Bij_on (λ (k : a ⟶ x), (k ∘ i.hom : a' ⟶ x)) univ univ :=
Bij_on.of_equiv $ show (a ⟶ x) ≃ (a' ⟶ x), from
{ to_fun := λ k, k ∘ i.hom,
  inv_fun := λ k', k' ∘ i.inv,
  left_inv := λ k, by simp,
  right_inv := λ k', by simp }

parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
parameters {a' b'₀ b'₁ : C} (f'₀ : a' ⟶ b'₀) (f'₁ : a' ⟶ b'₁)
parameters (i : iso a' a) (j₀ : iso b'₀ b₀) (j₁ : iso b'₁ b₁)
parameters (e₀ : f₀ ∘ i.hom = j₀.hom ∘ f'₀) (e₁ : f₁ ∘ i.hom = j₁.hom ∘ f'₁)

include e₀ e₁
def Is_pushout_of_isomorphic : Is_pushout f'₀ f'₁ (g₀ ∘ j₀.hom) (g₁ ∘ j₁.hom) :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁}
       : po.universal x
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | (p.1 ∘ j₀.hom) ∘ f'₀ = (p.2 ∘ j₁.hom) ∘ f'₁}
       : begin
           convert Bij_on.refl _, funext p, apply propext,
           rw [←assoc, ←assoc, ←e₀, ←e₁], simp
         end
  ...  ~~ {p : (b'₀ ⟶ x) × (b'₁ ⟶ x) | p.1 ∘ f'₀ = p.2 ∘ f'₁}
       : Bij_on.restrict''
           (Bij_on.prod' (precomposition_bij j₀) (precomposition_bij j₁))
           {p | p.1 ∘ f'₀ = p.2 ∘ f'₁},
  by convert this; funext; simp
omit e₀ e₁

parameters {c' : C} (k : iso c c')

def Is_pushout_of_isomorphic' : Is_pushout f₀ f₁ (k.hom ∘ g₀) (k.hom ∘ g₁) :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ univ
       : precomposition_bij k
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁ }
       : po.universal x,
  by convert this; funext; simp

end isomorphic

section pushout_tranpose

parameters {C : Type u} [cat : category.{v} C]
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

parameters {c' : C} {g₀' : b₀ ⟶ c'} {g₁' : b₁ ⟶ c'}
parameters (po' : Is_pushout f₁ f₀ g₁' g₀')
def Is_pushout.iso_transpose : c ≅ c' :=
pushout.unique po.transpose po'

@[simp] lemma Is_pushout.iso_transpose_map₀ : g₀ ≫ (po.iso_transpose po').hom = g₀' :=
by apply pushout.unique_commutes₁

@[simp] lemma Is_pushout.iso_transpose_map₁ : g₁ ≫ (po.iso_transpose po').hom = g₁' :=
by apply pushout.unique_commutes₀

lemma Is_pushout.transpose_induced {x : C} {h₀ : b₀ ⟶ x} {h₁ : b₁ ⟶ x} {e : f₀ ≫ h₀ = f₁ ≫ h₁} :
  (po.iso_transpose po').hom ≫ po'.induced h₁ h₀ e.symm = po.induced h₀ h₁ e :=
begin
  symmetry,
  apply pushout_induced_eq_iff; rw ←assoc; simp
end

end pushout_tranpose

section pushout_initial
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}

-- TODO: Somehow prove these two simultaneously?
def Is_pushout_of_Is_coproduct_of_Is_initial (copr : Is_coproduct g₀ g₁)
  (h : Is_initial_object.{v} a) : Is_pushout f₀ f₁ g₀ g₁ :=
Is_pushout.mk $ λ x, calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | true}
       : Bij_on.of_Is_equiv (copr.universal x)
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁}
       : by convert Bij_on.refl _; ext p; change (_ = _) ↔ true;
            simp; apply h.uniqueness

def Is_coproduct_of_Is_pushout_of_Is_initial (po : Is_pushout f₀ f₁ g₀ g₁)
  (h : Is_initial_object.{v} a) : Is_coproduct g₀ g₁ :=
have _ := λ x, calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁}
       : po.universal x
  ...  ~~ (univ : set ((b₀ ⟶ x) × (b₁ ⟶ x)))
       : begin
           convert Bij_on.refl _, symmetry, rw ←univ_subset_iff,
           intros p _, apply h.uniqueness
         end,
Is_coproduct.mk $ λ x, (this x).Is_equiv

end pushout_initial

section coprod_of_pushouts

parameters {C : Type u} [cat : category.{v} C] [co : has_coproducts.{v} C]
include cat co
parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
parameters {a' b₀' b₁' c' : C} {f₀' : a' ⟶ b₀'} {f₁' : a' ⟶ b₁'}
parameters {g₀' : b₀' ⟶ c'} {g₁' : b₁' ⟶ c'} (po' : Is_pushout f₀' f₁' g₀' g₁')
include po po'

def Is_pushout_coprod :
  Is_pushout
    (coprod_of_maps f₀ f₀') (coprod_of_maps f₁ f₁')
    (coprod_of_maps g₀ g₀') (coprod_of_maps g₁ g₁') :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ (univ : set ((c ⟶ x) × (c' ⟶ x)))
       : Bij_on.of_Is_equiv ((has_coproducts.coproduct c c').is_coproduct.universal x)
  ...  ~~ {pp : ((b₀ ⟶ x) × (b₁ ⟶ x)) × ((b₀' ⟶ x) × (b₁' ⟶ x))
          | pp.1.1 ∘ f₀ = pp.1.2 ∘ f₁ ∧ pp.2.1 ∘ f₀' = pp.2.2 ∘ f₁'}
       :
  begin
    convert Bij_on.prod (po.universal x) (po'.universal x),
    ext p, simp
  end
  ...  ~~ {qq : ((b₀ ⟶ x) × (b₀' ⟶ x)) × ((b₁ ⟶ x) × (b₁' ⟶ x))
          | qq.1.1 ∘ f₀ = qq.2.1 ∘ f₁ ∧ qq.1.2 ∘ f₀' = qq.2.2 ∘ f₁'}
       : Bij_on.restrict_equiv
           { to_fun := λ (pp : ((b₀ ⟶ x) × (b₁ ⟶ x)) × ((b₀' ⟶ x) × (b₁' ⟶ x))), ((pp.1.1, pp.2.1), (pp.1.2, pp.2.2)),
             inv_fun := λ qq, ⟨⟨qq.1.1, qq.2.1⟩, ⟨qq.1.2, qq.2.2⟩⟩,
             left_inv := assume ⟨⟨_,_⟩,⟨_,_⟩⟩, rfl,
             right_inv := assume ⟨⟨_,_⟩,⟨_,_⟩⟩, rfl }
           {qq : ((b₀ ⟶ x) × (b₀' ⟶ x)) × ((b₁ ⟶ x) × (b₁' ⟶ x))
          | qq.1.1 ∘ f₀ = qq.2.1 ∘ f₁ ∧ qq.1.2 ∘ f₀' = qq.2.2 ∘ f₁'}
  ...  ~~ {qq : ((b₀ ⟶ x) × (b₀' ⟶ x)) × ((b₁ ⟶ x) × (b₁' ⟶ x))
          | coprod.induced qq.1.1 qq.1.2 ∘ coprod_of_maps f₀ f₀' =
            coprod.induced qq.2.1 qq.2.2 ∘ coprod_of_maps f₁ f₁' }
       :
  begin
    convert Bij_on.refl _,
    ext qq, change _ = _ ↔ _ = _ ∧ _ = _,
    rw [coprod.ext, ←assoc, ←assoc, ←assoc, ←assoc],
    simp
  end
  ...  ~~ {qq : (b₀ ⊔ b₀' ⟶ x) × (b₁ ⊔ b₁' ⟶ x)
          | qq.1 ∘ coprod_of_maps f₀ f₀' = qq.2 ∘ coprod_of_maps f₁ f₁'}
       : Bij_on.restrict''
           (Bij_on.prod'
             (Bij_on.of_Is_equiv coprod.induced_Is_equiv)
             (Bij_on.of_Is_equiv coprod.induced_Is_equiv))
           {qq : (b₀ ⊔ b₀' ⟶ x) × (b₁ ⊔ b₁' ⟶ x)
           | qq.1 ∘ coprod_of_maps f₀ f₀' = qq.2 ∘ coprod_of_maps f₁ f₁'},
  begin
    convert this,
    funext k, apply prod.ext; apply coprod.uniqueness;
    { change _ ∘ _ ∘ _ = _ ∘ _, simp [coproduct_comparison],
      rw ←assoc, simp, refl },
  end

end coprod_of_pushouts

section pushout_i

parameters {C : Type u} [cat : category.{v} C] [co : has_coproducts.{v} C]
include cat co
-- Obviously we shouldn't really need C to have an initial object here, but oh well
parameters [has_initial_object.{v} C]
parameters {a b c : C} (f : a ⟶ b)

/-
  a → a ⊔ c
  ↓     ↓
  b → b ⊔ c
-/

def Is_pushout_i₀ : Is_pushout f i₀ i₀ (coprod_of_maps f (𝟙 c)) :=
let po := Is_pushout_coprod (Is_pushout.refl f) (Is_pushout.refl (! c)).transpose in
by convert Is_pushout_of_isomorphic po f i₀
     (coprod_initial_right a) (coprod_initial_right b) (iso.refl _) _ _; simp

/-
  a → c ⊔ a
  ↓     ↓
  b → c ⊔ b
-/

def Is_pushout_i₁ : Is_pushout f i₁ i₁ (coprod_of_maps (𝟙 c) f) :=
let po := Is_pushout_coprod (Is_pushout.refl (! c)).transpose (Is_pushout.refl f) in
by convert Is_pushout_of_isomorphic po f i₁
     (coprod_initial_left a) (coprod_initial_left b) (iso.refl _) _ _; simp

end pushout_i

section pushout_swap
parameters {C : Type u} [cat : category.{v} C]
include cat
parameters {a b c : C} {f : a ⟶ b} {g₀ g₁ : b ⟶ c} (po : Is_pushout f f g₀ g₁)

def Is_pushout.swap : c ⟶ c := po.induced g₁ g₀ po.commutes.symm

def Is_pushout.swap_iso : c ≅ c :=
{ hom := po.swap,
  inv := po.swap,
  hom_inv_id' := by apply po.uniqueness; unfold Is_pushout.swap; rw ←assoc; simp,
  inv_hom_id' := by apply po.uniqueness; unfold Is_pushout.swap; rw ←assoc; simp }

@[simp] def Is_pushout.induced_swap {x} {h₀ h₁ : b ⟶ x} {p p'} :
  po.induced h₀ h₁ p ∘ po.swap = po.induced h₁ h₀ p' :=
by apply po.uniqueness; unfold Is_pushout.swap; rw ←assoc; simp

end pushout_swap

section pushout_of_maps
parameters {C : Type u} [cat : category.{v} C]
include cat
variables {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
variables {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)
variables {a' b₀' b₁' c' : C} {f₀' : a' ⟶ b₀'} {f₁' : a' ⟶ b₁'}
variables {g₀' : b₀' ⟶ c'} {g₁' : b₁' ⟶ c'} (po' : Is_pushout f₀' f₁' g₀' g₁')
variables {a'' b₀'' b₁'' c'' : C} {f₀'' : a'' ⟶ b₀''} {f₁'' : a'' ⟶ b₁''}
variables {g₀'' : b₀'' ⟶ c''} {g₁'' : b₁'' ⟶ c''} (po'' : Is_pushout f₀'' f₁'' g₀'' g₁'')
variables (ha : a ⟶ a') (hb₀ : b₀ ⟶ b₀') (hb₁ : b₁ ⟶ b₁')
variables (h₀ : hb₀ ∘ f₀ = f₀' ∘ ha) (h₁ : hb₁ ∘ f₁ = f₁' ∘ ha)
variables (ka : a' ⟶ a'') (kb₀ : b₀' ⟶ b₀'') (kb₁ : b₁' ⟶ b₁'')
variables (k₀ : kb₀ ∘ f₀' = f₀'' ∘ ka) (k₁ : kb₁ ∘ f₁' = f₁'' ∘ ka)

include po po' h₀ h₁

def pushout_of_maps : c ⟶ c' :=
po.induced (g₀' ∘ hb₀) (g₁' ∘ hb₁)
  (by rw [←assoc, ←assoc, h₀, h₁]; simp [po'.commutes])

omit po po' h₀ h₁

lemma induced_pushout_of_maps {x : C} {k₀ : b₀' ⟶ x} {k₁ : b₁' ⟶ x} {e} :
  po'.induced k₀ k₁ e ∘ pushout_of_maps po po' ha hb₀ hb₁ h₀ h₁ = po.induced (k₀ ∘ hb₀) (k₁ ∘ hb₁)
    (by rw [←assoc, ←assoc, h₀, h₁]; simp [e]) :=
begin
  unfold pushout_of_maps,
  apply po.uniqueness; { rw ←assoc, simp }
end

@[simp] lemma pushout_of_maps_commutes₀ : pushout_of_maps po po' ha hb₀ hb₁ h₀ h₁ ∘ g₀ = g₀' ∘ hb₀ :=
by simp [pushout_of_maps]

@[simp] lemma pushout_of_maps_commutes₁ : pushout_of_maps po po' ha hb₀ hb₁ h₀ h₁ ∘ g₁ = g₁' ∘ hb₁ :=
by simp [pushout_of_maps]

lemma pushout_of_maps_id : pushout_of_maps po po (𝟙 a) (𝟙 b₀) (𝟙 b₁) (by simp) (by simp) = 𝟙 _ :=
by apply pushout_induced_eq_iff; simp

lemma pushout_of_maps_comp :
  pushout_of_maps po po'' (ha ≫ ka) (hb₀ ≫ kb₀) (hb₁ ≫ kb₁)
    (by rw [←assoc, h₀, assoc, k₀, ←assoc]) (by rw [←assoc, h₁, assoc, k₁, ←assoc]) =
  pushout_of_maps po po' ha hb₀ hb₁ h₀ h₁ ≫ pushout_of_maps po' po'' ka kb₀ kb₁ k₀ k₁ :=
by apply pushout_induced_eq_iff; rw ←assoc; simp

end pushout_of_maps

end category_theory
