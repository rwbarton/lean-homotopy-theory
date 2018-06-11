import categories.colimit_lemmas
import homotopy_theory.formal.cylinder.hep

import .category
import .cylinder
import .homeomorphism
import .inter_union
import .smush

noncomputable theory

open set

open categories
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

def pair.homeomorphism.is_of_pairs' (h : pair.homeomorphism P Q) : A = h.h.equiv ⁻¹' B :=
h.is_of_pairs

def pair.homeomorphism.on_subspaces (h : P ≅ₚ Q) : homeomorphism A' B' :=
h.h.restrict h.is_of_pairs

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

-- Maybe we should have made `pair` a category
def pair.prod.congr_right (h : Q ≅ₚ R) : P ⊗ Q ≅ₚ P ⊗ R :=
pair.homeomorphism.mk
  { morphism := Top.prod_maps 1 h.h,
    inverse := Top.prod_maps 1 h.h.symm,
    witness_1 := begin
      ext pq, cases pq with p q,
      change (p, h.h.equiv.symm (h.h.equiv q)) = (p, q),
      simp
    end,
    witness_2 := begin
      ext pr, cases pr with p r,
      change (p, h.h.equiv (h.h.equiv.symm r)) = (p, r),
      simp
    end}
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
{ morphism :=
    Top.mk_hom
      (λ p, ⟨(p.1.val, p.2.val), ⟨p.1.property, p.2.property⟩⟩)
      (by continuity),
  inverse :=
    Top.mk_hom
      (λ p, (⟨p.val.1, p.property.left⟩, ⟨p.val.2, p.property.right⟩))
      (by continuity),
  witness_1 := by ext p; rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨a, b⟩, ⟨ha, hb⟩⟩; refl }

protected def pair.l1 : homeomorphism (Top.prod A' Y) (Top.mk_ob {p : XY | p.1 ∈ A}) :=
{ morphism := Top.mk_hom (λ p, ⟨(p.1.val, p.2), p.1.property⟩) (by continuity),
  inverse := Top.mk_hom (λ p, (⟨p.val.1, p.property⟩, p.val.2)) (by continuity),
  witness_1 := by ext p; rcases p with ⟨⟨a, ha⟩, y⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨a, y⟩, ha⟩; refl }

protected def pair.l2 : homeomorphism (Top.prod X B') (Top.mk_ob {p : XY | p.2 ∈ B}) :=
{ morphism := Top.mk_hom (λ p, ⟨(p.1, p.2.val), p.2.property⟩) (by continuity),
  inverse := Top.mk_hom (λ p, (p.val.1, ⟨p.val.2, p.property⟩)) (by continuity),
  witness_1 := by ext p; rcases p with ⟨x, ⟨b, hb⟩⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨x, b⟩, hb⟩; refl }

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

def pair.admits_retract : Prop := ∃ r : X ⟶ A', r ∘ P.incl = 1

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
lemma admits_retract_congr (h : pair.homeomorphism P Q) :
  P.admits_retract → Q.admits_retract :=
assume ⟨r, hr⟩,
⟨h.on_subspaces.morphism ∘ r ∘ h.h.inverse, calc
  h.on_subspaces.morphism ∘ r ∘ h.h.inverse ∘ Q.incl
    = h.on_subspaces.morphism ∘ r ∘ h.h.inverse ∘
      (Q.incl ∘ h.on_subspaces.morphism) ∘ h.on_subspaces.inverse      : by simp
... = h.on_subspaces.morphism ∘ (r ∘ P.incl) ∘ h.on_subspaces.inverse
    : by simp [pair.homeomorphism.on_subspaces, homeomorphism.restriction_commutes]
... = 𝟙 _  : by rw hr; simp⟩

lemma prod_empty_admits_retract (K : Top) :
  P.admits_retract → (P ⊗ pair.mk K ∅).admits_retract :=
assume ⟨r, hr⟩,
let r' : Top.prod X K ⟶ (P ⊗ pair.mk K ∅).subspace :=
  pair.j₀ P (pair.mk K ∅) ∘ Top.prod_maps r 1 in
begin
  existsi r',
  ext p, rcases p with ⟨⟨a, k⟩, h|⟨⟨⟩⟩⟩,
  apply subtype.eq,
  change ((r a).val, k) = (a, k), congr,
  exact congr_arg subtype.val (@@Top.hom_congr hr ⟨a, h⟩),
end

-- A condition for the product of closed pairs to be
-- cofibered. Actually, P and Q only need to be cofibered (and only
-- one of them needs to be closed); see [Strøm, Note on Cofibrations
-- II, Theorem 6]. The argument is more intricate and the statement
-- below will suffice for our purposes. We'll show that (Dⁿ, Sⁿ⁻¹)
-- satisfies the hypothesis on Q.
lemma prod_cofibered (ha : is_closed A) (hb : is_closed B)
  (hq : Q ⊗ I_0 ≅ₚ pair.mk Y ∅ ⊗ I_0) :
  P.cofibered → (P ⊗ Q).cofibered :=
let Q' := pair.mk Y ∅ in
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

def smush : unit_disk_sphere V ⊗ I_0 ≅ₚ pair.mk (unit_disk V) ∅ ⊗ I_0 :=
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
prod_cofibered P _ ha (is_closed_eq (by continuity) continuous_const) (smush V)

end smush

end cofibered

end homotopy_theory.topological_spaces
