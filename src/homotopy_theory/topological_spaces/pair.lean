import category_theory.colimit_lemmas
import homotopy_theory.formal.cylinder.hep

import .category
import .colimits
import .cylinder
import .homeomorphism
import .inter_union
import .smush

noncomputable theory

open set

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{0}

structure pair :=
(space : Top)
(subset : set space)

variables (P Q R : pair)
-- TODO: Is this too weird?
local notation `X` := P.space
local notation `A` := P.subset
local notation `Y` := Q.space
local notation `B` := Q.subset
local notation `Z` := R.space
local notation `C` := R.subset

-- The subspace component of a pair, considered as a space.
def pair.subspace := Top.mk_ob A

local notation `A'` := P.subspace
local notation `B'` := Q.subspace

-- The inclusion of the subspace, considered as a morphism of Top.
@[reducible] def pair.incl : A' ⟶ X := incl A

section homeomorphism

def Top.homeomorphism.of_pairs (h : homeomorphism X Y) : Prop := A = h ⁻¹' B
structure pair.homeomorphism :=
(h : homeomorphism X Y)
(is_of_pairs : h.of_pairs P Q)

notation P ` ≅ₚ ` Q := pair.homeomorphism P Q

variables {P Q R}
include P Q

lemma pair.homeomorphism.is_of_pairs' (h : P ≅ₚ Q) : A = h.h.equiv ⁻¹' B :=
h.is_of_pairs

lemma pair.homeomorphism.is_of_pairs.mk' (h : homeomorphism X Y)
  (ha : ∀ a ∈ A, h a ∈ B) (hb : ∀ b ∈ B, h.symm b ∈ A) : h.of_pairs P Q :=
begin
  ext p, split, { exact ha p },
  { intro hp, apply function.comp _ (hb (h p)) hp,
    change h.equiv.symm (h.equiv p) ∈ _ → p ∈ _,
    simp }
end

def pair.homeomorphism.on_subspaces (h : P ≅ₚ Q) : homeomorphism A' B' :=
h.h.restrict h.is_of_pairs

lemma is_closed_congr (h : P ≅ₚ Q) : is_closed A ↔ is_closed B :=
by rw [h.is_of_pairs', h.h.is_closed_iff]; refl

@[symm] def pair.homeomorphism.symm (h : P ≅ₚ Q) : Q ≅ₚ P :=
pair.homeomorphism.mk h.h.symm $
  show B = h.h.equiv.symm ⁻¹' A, from
  by rw [h.is_of_pairs', ←preimage_comp]; simp [preimage_id]

include R

@[trans] def pair.homeomorphism.trans (h₁ : P ≅ₚ Q) (h₂ : Q ≅ₚ R) : P ≅ₚ R :=
pair.homeomorphism.mk (h₁.h.trans h₂.h) $
  show A = (function.comp h₂.h.equiv h₁.h.equiv) ⁻¹' C, from
  by rw [preimage_comp, h₁.is_of_pairs', h₂.is_of_pairs']

end homeomorphism

@[reducible] def pair.empty (W : Top) : pair := pair.mk W ∅

section prod

def pair.prod : pair :=
pair.mk (Top.prod X Y) {p | p.1 ∈ A ∨ p.2 ∈ B}

notation P ` ⊗ `:35 Q:34 := pair.prod P Q

variables {P Q R}
include P Q

lemma pair.prod.is_closed (ha : is_closed A) (hb : is_closed B) :
  is_closed (P ⊗ Q).subset :=
is_closed_union
   (continuous_iff_is_closed.mp continuous_fst _ ha)
   (continuous_iff_is_closed.mp continuous_snd _ hb)

lemma prod_comm_is_of_pairs : prod_comm.of_pairs (P ⊗ Q) (Q ⊗ P) :=
by ext pq; cases pq; exact or.comm

def pair.prod_comm : P ⊗ Q ≅ₚ Q ⊗ P :=
pair.homeomorphism.mk prod_comm prod_comm_is_of_pairs

include R

lemma prod_assoc_is_of_pairs : prod_assoc.of_pairs ((P ⊗ Q) ⊗ R) (P ⊗ (Q ⊗ R)) :=
by ext pqr; rcases pqr with ⟨⟨p, q⟩, r⟩; exact or.assoc

def pair.prod_assoc : (P ⊗ Q) ⊗ R ≅ₚ P ⊗ (Q ⊗ R) :=
pair.homeomorphism.mk prod_assoc prod_assoc_is_of_pairs

-- Maybe we should have made `pair` a category and P ⊗ - a functor
def pair.prod.congr_right (h : Q ≅ₚ R) : P ⊗ Q ≅ₚ P ⊗ R :=
pair.homeomorphism.mk h.h.prod_congr_right
  begin
    ext pq, cases pq with p q,
    change p ∈ A ∨ q ∈ B ↔ p ∈ A ∨ q ∈ h.h.equiv ⁻¹' C,
    rw h.is_of_pairs'
  end

end prod

section pushout

/-

If A and B are closed, then there is a pushout square

  A × B → X × B
    ↓       ↓
  A × Y → (P ⊗ Q).subspace = A × Y ∪ X × B.

Note that A × B here denotes the product of the (sub)spaces A and B,
not the subspace of X × Y on the product of the subsets A and B; and
the same for A × Y and X × B.

-/

variables (ha : is_closed A) (hb : is_closed B)

-- TODO: product bifunctor
protected def pair.i₀ : Top.prod A' B' ⟶ Top.prod A' Y :=
Top.mk_hom (λ p, (p.1, p.2.val)) (by continuity)

protected def pair.i₁ : Top.prod A' B' ⟶ Top.prod X B' :=
Top.mk_hom (λ p, (p.1.val, p.2)) (by continuity)

protected def pair.j₀ : Top.prod A' Y ⟶ (P ⊗ Q).subspace :=
Top.mk_hom (λ p, ⟨(p.1.val, p.2), or.inl p.1.property⟩)
  (by continuity)

protected def pair.j₁ : Top.prod X B' ⟶ (P ⊗ Q).subspace :=
Top.mk_hom (λ p, ⟨(p.1, p.2.val), or.inr p.2.property⟩)
  (by continuity)

local notation `XY` := Top.prod X Y

-- Establish an isomorphism to the intersection-union pushout square
-- of subspaces of X × Y.
protected def pair.k : homeomorphism (Top.prod A' B') (Top.mk_ob {p : XY | p.1 ∈ A ∧ p.2 ∈ B}) :=
{ hom :=
    Top.mk_hom
      (λ p, ⟨(p.1.val, p.2.val), ⟨p.1.property, p.2.property⟩⟩)
      (by continuity),
  inv :=
    Top.mk_hom
      (λ p, (⟨p.val.1, p.property.left⟩, ⟨p.val.2, p.property.right⟩))
      (by continuity),
  hom_inv_id' := by ext p; rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; refl,
  inv_hom_id' := by ext p; rcases p with ⟨⟨a, b⟩, ⟨ha, hb⟩⟩; refl }

protected def pair.l1 : homeomorphism (Top.prod A' Y) (Top.mk_ob {p : XY | p.1 ∈ A}) :=
{ hom := Top.mk_hom (λ p, ⟨(p.1.val, p.2), p.1.property⟩) (by continuity),
  inv := Top.mk_hom (λ p, (⟨p.val.1, p.property⟩, p.val.2)) (by continuity),
  hom_inv_id' := by ext p; rcases p with ⟨⟨a, ha⟩, y⟩; refl,
  inv_hom_id' := by ext p; rcases p with ⟨⟨a, y⟩, ha⟩; refl }

protected def pair.l2 : homeomorphism (Top.prod X B') (Top.mk_ob {p : XY | p.2 ∈ B}) :=
{ hom := Top.mk_hom (λ p, ⟨(p.1, p.2.val), p.2.property⟩) (by continuity),
  inv := Top.mk_hom (λ p, (p.val.1, ⟨p.val.2, p.property⟩)) (by continuity),
  hom_inv_id' := by ext p; rcases p with ⟨x, ⟨b, hb⟩⟩; refl,
  inv_hom_id' := by ext p; rcases p with ⟨⟨x, b⟩, hb⟩; refl }

protected def pair.po :
  Is_pushout (pair.i₀ P Q) (pair.i₁ P Q) (pair.j₀ P Q) (pair.j₁ P Q) :=
Is_pushout_of_isomorphic
  (@Is_pushout_inter_union (Top.prod X Y) _ _
    (continuous_iff_is_closed.mp continuous_fst _ ha)
    (continuous_iff_is_closed.mp continuous_snd _ hb))
  (pair.i₀ P Q) (pair.i₁ P Q)
  (pair.k P Q) (pair.l1 P Q) (pair.l2 P Q) (by funext; refl) (by funext; refl)

end pushout

section interval

def I_0 : pair := pair.mk I01 {0}
instance I_0.subspace.has_zero : has_zero I_0.subspace :=
⟨⟨(0 : I01), mem_singleton _⟩⟩

def I_0.subspace.singleton : * ≃ I_0.subspace :=
{ to_fun := λ _, 0,
  inv_fun := λ _, punit.star,
  left_inv := λ ⟨⟩, rfl,
  right_inv := λ z, show 0 = z, from subtype.eq (mem_singleton_iff.mp z.property).symm }

end interval

section cofibered

open homotopy_theory.cylinder
local notation `i` := i.{1 0}

-- A pair is cofibered if the inclusion of the subspace is a
-- cofibration.
def pair.cofibered : Prop := hep 0 P.incl

lemma pair.empty_cofibered (W : Top) : (pair.empty W).cofibered :=
have Is_initial_object.{1 0} (pair.empty W).subspace, from
  Top.is_initial_object_of_to_empty _ (by intro p; rcases p with ⟨_,⟨⟩⟩),
hep_initial_induced 0 this
  (preserves_initial_object.Is_initial_object_of_Is_initial_object I.{1 0} this)

def pair.admits_retract : Prop := ∃ r : X ⟶ A', r ∘ P.incl = 𝟙 A'

-- A pair (X, A) is cofibered if and only if the inclusion map of the
-- pair (X × I, A × I ∪ X × {0}) admits a retract.
--
-- This result holds even without the assumption that A is closed; see
-- [Strøm, Note on Cofibrations II, Theorem 2]. However, a more
-- intricate argument is then needed to show that A × I ∪ X × {0} is a
-- pushout when (X, A) is cofibered.
lemma pair.cofibered_iff (ha : is_closed A) :
  P.cofibered ↔ (P ⊗ I_0).admits_retract :=
have po : _ := pair.po P I_0 ha (is_closed_singleton : is_closed (_ : set I01)),
have po' : _ :=
  Is_pushout_of_isomorphic po
    (i 0 @> P.subspace) P.incl
    (prod_singleton I_0.subspace.singleton)
    (homeomorphism.refl _)
    (prod_singleton I_0.subspace.singleton)
    (by ext; refl) (by ext; refl),
iff.trans (homotopy_theory.cylinder.hep_iff_pushout_retract 0 po'.transpose) $ begin
  have : pair.incl (P ⊗ I_0) = po'.transpose.induced (i 0 @> X) (I &> pair.incl P) _, {
    apply po'.uniqueness,
    { rw [Is_pushout.induced_commutes₁], refl },
    { rw [Is_pushout.induced_commutes₀], refl },
  },
  unfold pair.admits_retract, rw this, refl
end

variables {P Q}
-- TODO: Should these be ↔?
lemma admits_retract_congr (h : P ≅ₚ Q) : P.admits_retract → Q.admits_retract :=
assume ⟨r, hr⟩,
⟨h.on_subspaces.hom ∘ r ∘ h.h.inv, calc
  h.on_subspaces.hom ∘ r ∘ h.h.inv ∘ Q.incl
    = h.on_subspaces.hom ∘ r ∘ h.h.inv ∘
      (Q.incl ∘ h.on_subspaces.hom) ∘ h.on_subspaces.inv      : by simp
... = h.on_subspaces.hom ∘ (r ∘ P.incl) ∘ h.on_subspaces.inv
    : by simp [pair.homeomorphism.on_subspaces, homeomorphism.restriction_commutes]
... = 𝟙 _  : by rw hr; simp⟩

lemma cofibered_congr (h : P ≅ₚ Q) (ha : is_closed A) : P.cofibered → Q.cofibered :=
have P ⊗ I_0 ≅ₚ Q ⊗ I_0, from calc
  P ⊗ I_0 ≅ₚ I_0 ⊗ P  : pair.prod_comm
  ...     ≅ₚ I_0 ⊗ Q  : pair.prod.congr_right h -- TODO: congr_left
  ...     ≅ₚ Q ⊗ I_0  : pair.prod_comm,
calc
  P.cofibered
    → (P ⊗ I_0).admits_retract  : (P.cofibered_iff ha).mp
... → (Q ⊗ I_0).admits_retract  : admits_retract_congr this
... → Q.cofibered               : (Q.cofibered_iff ((is_closed_congr h).mp ha)).mpr

lemma prod_empty_admits_retract (K : Top) :
  P.admits_retract → (P ⊗ pair.empty K).admits_retract :=
assume ⟨r, hr⟩,
let r' : Top.prod X K ⟶ (P ⊗ pair.empty K).subspace :=
  pair.j₀ P (pair.empty K) ∘ Top.prod_maps r (𝟙 K) in
begin
  existsi r',
  ext p; rcases p with ⟨⟨a, k⟩, h|⟨⟨⟩⟩⟩,
  { change (r a).val = a,
    exact congr_arg subtype.val (@@Top.hom_congr hr ⟨a, h⟩) },
  { refl }
end

-- A condition for the product of closed pairs to be
-- cofibered. Actually, P and Q only need to be cofibered (and only
-- one of them needs to be closed); see [Strøm, Note on Cofibrations
-- II, Theorem 6]. The argument is more intricate and the statement
-- below will suffice for our purposes. We'll show that (Dⁿ, Sⁿ⁻¹)
-- satisfies the hypothesis on Q.
lemma prod_cofibered (ha : is_closed A) (hb : is_closed B)
  (hq : Q ⊗ I_0 ≅ₚ pair.empty Y ⊗ I_0) :
  P.cofibered → (P ⊗ Q).cofibered :=
let Q' := pair.empty Y in
have _ := calc
  (P ⊗ I_0) ⊗ Q'
    ≅ₚ P ⊗ (I_0 ⊗ Q')  : pair.prod_assoc
... ≅ₚ P ⊗ (Q' ⊗ I_0)  : pair.prod.congr_right pair.prod_comm
... ≅ₚ P ⊗ (Q ⊗ I_0)   : pair.prod.congr_right hq.symm
... ≅ₚ (P ⊗ Q) ⊗ I_0   : pair.prod_assoc.symm,
calc
  P.cofibered
    → (P ⊗ I_0).admits_retract         : (pair.cofibered_iff P ha).mp
... → ((P ⊗ I_0) ⊗ Q').admits_retract  : prod_empty_admits_retract _
... → ((P ⊗ Q) ⊗ I_0).admits_retract   : admits_retract_congr this
... → (P ⊗ Q).cofibered  : (pair.cofibered_iff _ (pair.prod.is_closed ha hb)).mpr

section smush

variables (V : Type) [topological_space V] [smush.admissible' V]

def unit_disk : Top :=
Top.mk_ob (smush.unit_disk V)

def unit_disk_sphere : pair :=
pair.mk (unit_disk V) {v | smush.admissible.norm v.val = (1 : ℝ)}

lemma unit_disk_sphere.is_closed : is_closed (unit_disk_sphere V).subset :=
is_closed_eq (by continuity) continuous_const

def smush : unit_disk_sphere V ⊗ I_0 ≅ₚ pair.empty (unit_disk V) ⊗ I_0 :=
pair.homeomorphism.mk
  (homeomorphism.of_equiv (smush.H_equiv V)
    (smush.continuous_H V) (smush.continuous_vHv V))
  (begin
    change {p : unit_disk V × I01 | _ ∨ p.2 ∈ ({0} : set I01)} =
      (smush.H V) ⁻¹' {p : unit_disk V × I01 | p.1 ∈ ∅ ∨ p.2 ∈ ({0} : set I01)},
    convert smush.Ht0 V;
    { ext p, change _ ∨ _ ↔ _ ∨ _, apply or_congr (iff.refl _),
      rw mem_singleton_iff, apply subtype.ext },
  end)

lemma prod_disk_sphere_cofibered (ha : is_closed A) :
  P.cofibered → (P ⊗ unit_disk_sphere V).cofibered :=
prod_cofibered P _ ha (unit_disk_sphere.is_closed V) (smush V)

end smush

def I_01 := pair.mk I01 {0, 1}
def I_01_is_D1_S0 : I_01 ≅ₚ unit_disk_sphere ℝ :=
pair.homeomorphism.mk
  { hom :=
      Top.mk_hom
        (λ t,
          ⟨2 * t.val - 1,
           abs_le.mpr
             ⟨calc -1 = 2 * 0 - 1      : by norm_num
                  ... ≤ 2 * t.val - 1  : sub_le_sub_right (mul_le_mul_of_nonneg_left t.property.left (by norm_num)) _,
              calc 2 * t.val - 1 ≤ 2 * 1 - 1  : sub_le_sub_right (mul_le_mul_of_nonneg_left t.property.right (by norm_num)) _
                             ... = 1          : by norm_num⟩⟩)
        (by continuity),
    inv :=
      Top.mk_hom
        (λ t,
          ⟨(1 / 2) * (t.val + 1),
           mul_nonneg (by norm_num) (le_add_of_neg_add_le_right (abs_le.mp t.property).left),
           calc (1 / 2) * (t.val + 1) ≤ (1 / 2) * (1 + 1)  : mul_le_mul_of_nonneg_left (add_le_add_right (abs_le.mp t.property).right _) (by norm_num)
                                  ... = 1                  : by norm_num⟩)
        (by continuity),
    hom_inv_id' := begin
      ext t,
      change (1 / 2) * ((2 * t.val - 1) + 1) = t.val,
      ring
    end,
    inv_hom_id' := begin
      ext t,
      change 2 * ((1 / 2) * (t.val + 1)) - 1 = t.val,
      ring
    end }
  begin
    apply pair.homeomorphism.is_of_pairs.mk',
    { intros a ha, change a ∈ {(0 : I01), (1 : I01)} at ha,
      have ha' : a = (1 : I01) ∨ a = (0 : I01) := by simp at ha; exact ha,
      cases ha' with ha' ha',
      { subst ha', change abs (2 * (1 : ℝ) - 1) = 1, norm_num },
      { subst ha', change abs (2 * (0 : ℝ) - 1) = 1, norm_num } },
    { intros b hb, cases b with b hb', change abs b = 1 at hb,
      rw abs_eq at hb, swap, exact zero_le_one,
      cases hb with hb hb; change subtype.mk _ _ ∈ I_01.subset,
      { subst hb, have : (1 : I01) ∈ ({0, 1} : set I01), by simp, convert this, norm_num },
      { subst hb, have : (0 : I01) ∈ ({0, 1} : set I01), by simp, convert this, norm_num } }
  end

lemma I_01.is_closed : is_closed I_01.subset :=
(is_closed_congr I_01_is_D1_S0).mpr (unit_disk_sphere.is_closed ℝ)

lemma prod_I_01_cofibered (ha : is_closed A) :
  P.cofibered → (P ⊗ I_01).cofibered :=
calc
  P.cofibered
    → (P ⊗ unit_disk_sphere ℝ).cofibered
    : prod_disk_sphere_cofibered P ℝ ha
... → (P ⊗ I_01).cofibered
    : cofibered_congr (pair.prod.congr_right I_01_is_D1_S0.symm)
        (pair.prod.is_closed ha (unit_disk_sphere.is_closed ℝ))

end cofibered

end homotopy_theory.topological_spaces
