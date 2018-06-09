import .category
import .cofibrations
import .inter_union

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

variables (P Q : pair)
-- TODO: Is this too weird?
local notation `X` := P.space
local notation `A` := P.subset
local notation `Y` := Q.space
local notation `B` := Q.subset

-- The subspace component of a pair, considered as a space.
def pair.subspace := Top.mk_ob A

-- The inclusion of the subspace, considered as a morphism of Top.
def pair.incl : Top.mk_ob A ⟶ X := incl A

local notation `A'` := P.subspace
local notation `B'` := Q.subspace

def pair.prod : pair :=
pair.mk (Top.prod X Y) (set.prod A univ ∪ set.prod univ B)

notation P ` ⊗ ` Q := pair.prod P Q

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
Top.mk_hom (λ p, ⟨(p.1.val, p.2), or.inl ⟨p.1.property, trivial⟩⟩)
  (by continuity)

protected def pair.j₁ : Top.prod X B' ⟶ (P ⊗ Q).subspace :=
Top.mk_hom (λ p, ⟨(p.1, p.2.val), or.inr ⟨trivial, p.2.property⟩⟩)
  (by continuity)

-- Establish an isomorphism to the intersection-union pushout square
-- of subspaces of X × Y.
protected def pair.k : homeomorphism (Top.prod A' B') (Top.mk_ob (set.prod A univ ∩ set.prod univ B : set (Top.prod X Y))) :=
{ morphism :=
    Top.mk_hom
      (λ p, ⟨(p.1.val, p.2.val), ⟨⟨p.1.property, trivial⟩, ⟨trivial, p.2.property⟩⟩⟩)
      (by continuity),
  inverse :=
    Top.mk_hom
      (λ p, (⟨p.val.1, p.property.left.left⟩, ⟨p.val.2, p.property.right.right⟩))
      (by continuity),
  witness_1 := by ext p; rcases p with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨a, b⟩, ⟨ha, hb⟩⟩; refl }

protected def pair.l1 : homeomorphism (Top.prod A' Y) (Top.mk_ob (set.prod A univ : set (Top.prod X Y))) :=
{ morphism := Top.mk_hom (λ p, ⟨(p.1.val, p.2), ⟨p.1.property, trivial⟩⟩) (by continuity),
  inverse := Top.mk_hom (λ p, (⟨p.val.1, p.property.left⟩, p.val.2)) (by continuity),
  witness_1 := by ext p; rcases p with ⟨⟨a, ha⟩, y⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨a, y⟩, ha⟩; refl }

protected def pair.l2 : homeomorphism (Top.prod X B') (Top.mk_ob (set.prod univ B : set (Top.prod X Y))) :=
{ morphism := Top.mk_hom (λ p, ⟨(p.1, p.2.val), ⟨trivial, p.2.property⟩⟩) (by continuity),
  inverse := Top.mk_hom (λ p, (p.val.1, ⟨p.val.2, p.property.right⟩)) (by continuity),
  witness_1 := by ext p; rcases p with ⟨x, ⟨b, hb⟩⟩; refl,
  witness_2 := by ext p; rcases p with ⟨⟨x, b⟩, hb⟩; refl }

protected def pair.po :
  Is_pushout (pair.i₀ P Q) (pair.i₁ P Q) (pair.j₀ P Q) (pair.j₁ P Q) :=
Is_pushout_of_isomorphic
  (@Is_pushout_inter_union (Top.prod X Y) (set.prod A univ) (set.prod univ B)
    (is_closed_prod ha is_closed_univ) (is_closed_prod is_closed_univ hb))
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
def pair.cofibered : Prop := cofibration P.incl

def pair.admits_retract : Prop := ∃ r, r ∘ P.incl = 𝟙 _

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

end cofibered

end homotopy_theory.topological_spaces
