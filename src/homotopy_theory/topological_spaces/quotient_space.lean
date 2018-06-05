import data.pfun

import categories.colimits
import .category
import for_mathlib

/-

The quotient of a space by a subspace. Abstractly, this is given as
the pushout in the diagram

    A → *
  i ↓   ↓ j
    X → X/A
      q

We write X/A here, though the quotient space also depends on i and we
will not assume that i is an embedding or even injective. The space
X/A is equipped with a base point, the image of the map j.

Note that when A is empty, X/A is X with a disjoint base point
added. When A is nonempty, q : X → X/A is a quotient map.

* q restricts to a bijection of sets q' : X-A → X/A - *. We denote the
  latter set by X/A₋.

* The subset {*} of X/A is closed (open) if and only if A is closed
  (open) in X.

* In either of the above cases, q' is a homeomorphism.

-/

open categories set

universe u

namespace homotopy_theory.topological_spaces
local notation `Top` := Top.{u}

namespace construction
section
parameters {A X : Top} (i : A ⟶ X)
include i

-- We construct X/A as the quotient of X₊ by the equivalence relation
-- which identifies the added base point with everything in the image
-- of i : A → X.

inductive Xplus : Type u
| pt : Xplus
| k : X → Xplus
open Xplus
local attribute [elab_with_expected_type] Xplus.rec_on

local notation `X₊` := Xplus

instance Xplus.topological_space : topological_space X₊ :=
X.topology.coinduced k

def Aplus : set X₊ := insert pt (range (k ∘ i))
local notation `A₊` := Aplus

-- Two elements of X₊ are related either if they are equal, or if both
-- are either the base point or in the image of i : A → X.
def Xplus_rel (p₁ p₂ : X₊) : Prop := p₁ = p₂ ∨ p₁ ∈ A₊ ∧ p₂ ∈ A₊

lemma Xplus_rel.refl : reflexive Xplus_rel := assume p, or.inl rfl
lemma Xplus_rel.symm : symmetric Xplus_rel
| p₁ p₂ (or.inl e) := or.inl e.symm
| p₁ p₂ (or.inr a) := or.inr a.swap
lemma Xplus_rel.trans : transitive Xplus_rel :=
assume p₁ p₂ p₃ h₁ h₂,
  by unfold Xplus_rel; cases h₁; cases h₂; solve_by_elim { discharger := `[cc] }

instance Xplus.setoid : setoid Xplus :=
⟨Xplus_rel, Xplus_rel.refl, Xplus_rel.symm, Xplus_rel.trans⟩

@[simp] lemma Aplus_related (p₁ p₂ : X₊) (h₁ : p₁ ∈ A₊) (h₂ : p₂ ∈ A₊) : p₁ ≈ p₂ :=
or.inr ⟨h₁, h₂⟩

@[simp] lemma Aplus_pt : pt ∈ A₊ := by unfold Aplus; simp
@[simp] lemma Aplus_image (a : A) : k (i a) ∈ A₊ := by unfold Aplus; simp; tauto

def XmodA : Top := Top.mk_ob (quotient Xplus.setoid)
local notation `X/A` := XmodA

local notation `t` := Top.point_induced A

def q : X ⟶ X/A := Top.mk_hom (quotient.mk ∘ k)
def j : * ⟶ X/A := Top.mk_hom (λ _, quotient.mk pt) (by continuity)

lemma qi : q ∘ i = j ∘ t :=
by ext; funext a; apply quotient.sound; simp

section pushout
local notation f ` ∘ `:80 g:80 := g ≫ f

lemma commutes : q ∘ i = j ∘ t := subtype.eq qi

section induced
parameters (Z : Top) (h₀ : X ⟶ Z) (h₁ : * ⟶ Z) (e : h₀ ∘ i = h₁ ∘ t)
include e

def induced' : X₊ → Z :=
λ p, p.rec_on (h₁ punit.star) h₀

lemma induced'_ok (p p' : X₊) (h : p ≈ p') : induced' p = induced' p' :=
have ∀ q, q ∈ A₊ → induced' q = h₁ punit.star, from assume q hq, begin
  cases q, { refl },
  { simp [Aplus] at hq, cases hq with a h,
    subst q, exact Top.hom_congr e a }
end,
begin
  cases h, { subst h },
  { cases h with h h', rw [this p h, this p' h'] }
end

def induced : X/A ⟶ Z :=
Top.mk_hom (λ p, quotient.lift induced' induced'_ok p) (by continuity)

lemma induced_commutes₀ : induced ∘ q = h₀ :=
by ext; refl

lemma induced_commutes₁ : induced ∘ j = h₁ :=
by ext s; cases s; refl

end induced

lemma uniqueness (Z : Top) (k k' : X/A ⟶ Z)
  (e₀ : k ∘ q = k' ∘ q) (e₁ : k ∘ j = k' ∘ j) : k = k' :=
begin
  ext x,
  -- There is a bug when using the `induction` tactic with
  -- `quotient.ind`. Fortunately we can just as well use `quot.ind`.
  induction x using quot.ind,
  cases x,
  exact @@Top.hom_congr e₁ punit.star,
  exact @@Top.hom_congr e₀ _
end

def po : Is_pushout i t q j :=
Is_pushout.mk' commutes induced induced_commutes₀ induced_commutes₁ uniqueness

end pushout

local notation `*` := quotient.mk pt

lemma A_is_preimage_of_base_point : range i = q ⁻¹' {*} :=
have ∀ x, (∃ a, i a = x) ↔ q x = *, from assume x,
  show (∃ a, i a = x) ↔ quotient.mk (k x) = quotient.mk (pt),
  by rw quotient.eq; simp [(≈), setoid.r, Xplus_rel, Aplus],
by ext x; convert this x; simp

lemma A_closed_iff : is_closed (range i) ↔ is_closed ({*} : set X/A) :=
by rw A_is_preimage_of_base_point; refl

lemma A_open_iff : is_open (range i) ↔ is_open ({*} : set X/A) :=
by rw A_is_preimage_of_base_point; refl

def XminusA : set X := - range i
local notation `X-A` := XminusA

def XmodAminus : set X/A := - {*}
local notation `X/A₋` := XmodAminus

def q' : X-A → X/A₋ :=
assume x, ⟨q x.val, have x.val ∈ - range i := x.property,
  by rw A_is_preimage_of_base_point at this; simpa [XmodAminus]⟩

section q'_inv

lemma mem_XmodAminus_iff {p} : ⟦p⟧ ∈ XmodAminus ↔ p ∉ A₊ :=
by simp [XmodAminus, Aplus, (≈), setoid.r, Xplus_rel]; rw ←or_assoc; simp

-- This construction is very fragile for some reason
private def q'_inv0 : X₊ → roption (X-A) :=
λ p, p.rec_on roption.none (λ x, ⟨x ∉ range i, λ h, ⟨x, h⟩⟩)

private def q'_inv1 (p₀ : X/A) (hp₀ : p₀ ∈ X/A₋) : X-A :=
have ∀ (p : X₊), p ∈ A₊ → q'_inv0 p = roption.none, begin
  intros p hp, cases p, { refl },
  { simp [Aplus] at hp, cases hp, subst p,
    rw roption.eq_none_iff', dsimp [q'_inv0],
    apply not_not_intro, apply mem_range_self }
end,
have ok : ∀ (a b : X₊), a ≈ b → q'_inv0 a = q'_inv0 b, begin
  intros p p' h, cases h, { subst h },
  { cases h with h h', rw [this p h, this p' h'] }
end,
have ∀ (p : X₊), ⟦p⟧ ∈ X/A₋ → (q'_inv0 p).dom, from assume p h,
  have z : _ := mem_XmodAminus_iff.mp h,
  by cases p; dsimp [Aplus] at z; dsimp [q'_inv0]; simpa using z,
(quotient.lift q'_inv0 ok p₀).get
  (quotient.ind (assume p' h, this p' h) p₀ hp₀)

def q'_inv : X/A₋ → X-A :=
assume p, q'_inv1 p.val p.property

lemma q'_inv_q' (x) : q'_inv (q' x) = x :=
subtype.eq rfl

private lemma q'_q'_inv1 (p₀ hp₀) : q' (q'_inv ⟨p₀, hp₀⟩) = ⟨p₀, hp₀⟩ :=
have foo :  ∀ p hp, (q' (q'_inv ⟨⟦p⟧, hp⟩)).val = ⟦p⟧, from assume p hp,
  show q ((q'_inv0 p).get _) = ⟦p⟧, from
  begin
    cases p,
    { rw mem_XmodAminus_iff at hp, simpa using hp },
    refl
  end,
subtype.eq $ (quotient.ind foo p₀) hp₀

lemma q'_q'_inv (p) : q' (q'_inv p) = p := by cases p; apply q'_q'_inv1

end q'_inv

-- We have constructed an inverse (on the level of sets) for q', the
-- restriction of q to X-A.
def q'_equiv : X-A ≃ X/A₋ :=
{ to_fun := q',
  inv_fun := q'_inv,
  left_inv := q'_inv_q',
  right_inv := q'_q'_inv }

lemma q'_val (x : X-A) : (q'_equiv x).val = q x := rfl

-- Now we want to show that q' is a homeomorphism.

-- TODO: `continuity` doesn't directly work here because we need to
-- apply continuous.comp to break down the goal, but then one of the
-- new subgoals is `continuous q`, which is solved by applying
-- `continuous_id`! Maybe `apply_continuous.comp` should only fail if
-- `continuous_id` solves the first new goal?
lemma continuous_q' : continuous q' :=
begin
  continuity, apply continuous.comp; continuity
end

-- For continuity of q'_inv we need a hypothesis: A is open or closed.

-- Suppose A is closed. Then
-- U ⊆ X-A open → U ⊆ X open → q'(U) ⊆ X/A open → q'(U) ⊆ X/A₋ open.
-- So q' is an open map, hence q'_inv is continuous.
-- If A is open instead, replace "open" by "closed" throughout.

@[simp] lemma ugly_lemma (u : set X-A) :
  q ⁻¹' (subtype.val '' (q' '' u)) = subtype.val '' u :=
have subtype.val ∘ q' = q ∘ subtype.val := rfl,
begin
  rw [←image_comp, this, image_comp],
  apply subset.antisymm,
  { intros x h, rcases h with ⟨x', ⟨x'', h₁, h₂⟩, h₃⟩, refine ⟨x'', h₁, _⟩, subst x',
    have x''_x : Xplus_rel _ (k x''.val) (k x) := quotient.exact h₃, cases x''_x,
    { cc },
    { -- This case is impossible: x'' ∈ X-A but k x''.val ∈ A₊
      cases x''_x.left with h h, { simpa using h },
      { cases h with a h, have : i a = x''.val, by simpa using h,
        have bad := x''.property, rw ←this at bad, dsimp [XminusA] at bad,
        exact absurd (mem_range_self _) bad } } },
  apply subset_preimage_image
end

lemma q'_open_of_A_closed (ha : is_closed (range i)) {u : set X-A} (hu : is_open u) :
  is_open (q' '' u) :=
suffices is_open (subtype.val '' (q' '' u)), from
  let j : X/A₋ → X/A := subtype.val in
  have is_open (j ⁻¹' (j '' (q' '' u))) :=
    continuous_subtype_val _ this,
  by rwa preimage_image_eq _ injective_subtype_val at this,
show is_open (q ⁻¹' (subtype.val '' (q' '' u))), from
suffices is_open (subtype.val '' u), by simpa,
embedding_open embedding_subtype_val (by simpa using ha) hu

lemma q'_closed_of_A_open (ha : is_open (range i)) {u : set X-A} (hu : is_closed u) :
  is_closed (q' '' u) :=
suffices is_closed (subtype.val '' (q' '' u)), from
  let j : X/A₋ → X/A := subtype.val in
  have is_closed (j ⁻¹' (j '' (q' '' u))) :=
    continuous_iff_is_closed.mp continuous_subtype_val _ this,
  by rwa preimage_image_eq _ injective_subtype_val at this,
show is_closed (q ⁻¹' (subtype.val '' (q' '' u))), from
suffices is_closed (subtype.val '' u), by simpa,
have is_closed X-A := is_closed_compl_iff.mpr ha,
embedding_is_closed embedding_subtype_val (by simpa using this) hu

lemma continuous_q'_inv_of_A_closed (ha : is_closed (range i)) : continuous q'_inv :=
assume u hu,
  show is_open (q'_equiv.symm ⁻¹' u), from
  have _ := q'_open_of_A_closed ha hu,
  by rwa ←equiv.image_eq_preimage

lemma continuous_q'_inv_of_A_open (ha : is_open (range i)) : continuous q'_inv :=
continuous_iff_is_closed.mpr $ assume u hu,
  show is_closed (q'_equiv.symm ⁻¹' u), from
  have _ := q'_closed_of_A_open ha hu,
  by rwa ←equiv.image_eq_preimage

end
end construction

-- Interface to this module.
open construction

variables {A X : Top} (i : A ⟶ X)
-- The quotient space X/A (see preamble for more details).
def quotient_space : Top := XmodA i

-- The "quotient map" X → X/A. (Not an actual quotient map when A is
-- empty.)
def quotient_space.map : X ⟶ quotient_space i := q i

-- The base point of X/A.
def quotient_space.pt : quotient_space i := quotient.mk (Xplus.pt i)

@[reducible] def quotient_space.singleton_pt : set (quotient_space i) :=
{quotient_space.pt i}

theorem quotient_space_pt_is_closed_iff :
  is_closed (quotient_space.singleton_pt i) ↔ is_closed (range i) :=
(A_closed_iff i).symm

theorem quotient_space_pt_is_open_iff :
  is_open (quotient_space.singleton_pt i) ↔ is_open (range i) :=
(A_open_iff i).symm

-- X/A is the pushout of A → X along A → *.
def quotient_space.is_pushout :
  Is_pushout i (Top.point_induced A) (quotient_space.map i) (j i) :=
po i

-- The complementary space X-A.
def quotient_space.image_complement : Top := Top.mk_ob (XminusA i)

-- The space X/A with its base point removed.
def quotient_space.minus_base_point : Top := Top.mk_ob (XmodAminus i)

-- The map X-A → X/A - {*}.
def quotient_space.map_complement :
  quotient_space.image_complement i ⟶ quotient_space.minus_base_point i :=
Top.mk_hom (q' i) (continuous_q' i)

section inverse
-- For the inverse map to be continuous, we need a condition on A.
variables (h : is_closed (range i) ∨ is_open (range i))

-- Inverse to the above map.
def quotient_space.map_complement_inverse :
  quotient_space.minus_base_point i ⟶ quotient_space.image_complement i :=
Top.mk_hom (q'_inv i)
  (h.cases_on
    (assume h_closed, continuous_q'_inv_of_A_closed i h_closed)
    (assume h_open, continuous_q'_inv_of_A_open i h_open))

-- Verification that the above maps are inverses.
-- TODO: Use isomorphism in Top?
def quotient_space.map_complement_equiv :
  quotient_space.image_complement i ≃ quotient_space.minus_base_point i :=
q'_equiv i

end inverse

end homotopy_theory.topological_spaces
