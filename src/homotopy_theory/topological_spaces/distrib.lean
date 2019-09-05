import for_mathlib

import category_theory.colimit_lemmas

import .category
import .colimits
import .homeomorphism
import .inter_union
import .subspace

noncomputable theory

/-
The distributivity law in Top: X × Y ⊔ X × Z ≅ X × (Y ⊔ Z).
-/

open set
open category_theory

universe u

namespace homotopy_theory.topological_spaces
open homotopy_theory.topological_spaces.Top
local notation `Top` := Top.{u}

namespace distrib_private
section
parameters {X Y Z : Top}

def YZ := Y ⊔ Z
def inY : Y ⟶ Y ⊔ Z := i₀
def inZ : Z ⟶ Y ⊔ Z := i₁
def Y' := set.range inY
def Z' := set.range inZ
def Y_Y' : homeomorphism Y (Top.mk_ob Y') :=
homeomorphism_to_image_of_embedding (embedding_inl : embedding inY)
def Z_Z' : homeomorphism Z (Top.mk_ob Z') :=
homeomorphism_to_image_of_embedding (embedding_inr : embedding inZ)

def XYZ := Top.prod X (Y ⊔ Z)

def XY := {p : XYZ | p.2 ∈ Y'}
def XZ := {p : XYZ | p.2 ∈ Z'}

-- Verify closedness conditions for intersection-union pushout.

-- TODO: Move to mathlib?
def selector : YZ → bool
| (sum.inl _) := ff
| (sum.inr _) := tt

lemma continuous_selector : continuous selector :=
continuous_sum_rec
  (@continuous_const _ _ _ _ ff)
  (@continuous_const _ _ _ _ tt)

def Y'_closed : is_closed Y' :=
begin
  convert continuous_iff_is_closed.mp continuous_selector {ff} trivial,
  ext p, cases p,
  { change (∃ y, sum.inl y = sum.inl p) ↔ ff ∈ {ff}, simp },
  { change (∃ y, sum.inl y = sum.inr p) ↔ tt ∈ {ff}, simp }
end

def Z'_closed : is_closed Z' :=
begin
  convert continuous_iff_is_closed.mp continuous_selector {tt} trivial,
  ext p, cases p,
  { change (∃ z, sum.inr z = sum.inl p) ↔ ff ∈ {tt}, simp },
  { change (∃ z, sum.inr z = sum.inr p) ↔ tt ∈ {tt}, simp }
end

def XY_closed : is_closed XY :=
continuous_iff_is_closed.mp continuous_snd _ Y'_closed

def XZ_closed : is_closed XZ :=
continuous_iff_is_closed.mp continuous_snd _ Z'_closed

-- TODO: Eliminate duplication with pair.l2
def XxA_XA {B : Top} (A : set B) :
  homeomorphism (Top.prod X (Top.mk_ob A)) (Top.mk_ob {p : Top.prod X B | p.2 ∈ A}) :=
{ hom := Top.mk_hom (λ p, ⟨(p.1, p.2.val), p.2.property⟩) (by continuity),
  inv := Top.mk_hom (λ p, (p.val.1, ⟨p.val.2, p.property⟩)) (by continuity),
  hom_inv_id' := by ext p; rcases p with ⟨x, ⟨b, hb⟩⟩; refl,
  inv_hom_id' := by ext p; rcases p with ⟨⟨x, b⟩, hb⟩; refl }

def XxY_XY' : homeomorphism (Top.prod X Y) (Top.mk_ob XY) :=
Y_Y'.prod_congr_right.trans (XxA_XA Y')
def XxZ_XZ' : homeomorphism (Top.prod X Z) (Top.mk_ob XZ) :=
Z_Z'.prod_congr_right.trans (XxA_XA Z')

def po :=
Is_pushout_inter_of_cover XY XZ XY_closed XZ_closed
  begin
    rw ←univ_subset_iff, intros p _,
    rcases p with ⟨x, y|z⟩,
    { exact or.inl ⟨y, rfl⟩ },
    { exact or.inr ⟨z, rfl⟩ }
  end

def not_XY_and_XZ : XY ∩ XZ → pempty :=
λ q, false.elim $
  let ⟨p, ⟨y, py⟩, ⟨z, pz⟩⟩ := q in
  by change sum.inl y = p.2 at py; change sum.inr z = p.2 at pz; cc

def po' :=
Is_pushout_of_isomorphic po
  (Top.empty_induced (Top.prod X Y))
  (Top.empty_induced (Top.prod X Z))
  (initial_object.unique
    Top.empty_is_initial_object
    (Top.is_initial_object_of_to_empty (Top.mk_ob (XY ∩ XZ : set _)) not_XY_and_XZ))
  XxY_XY' XxZ_XZ'
  (Top.empty_is_initial_object.uniqueness _ _)
  (Top.empty_is_initial_object.uniqueness _ _)

def XxY_XYZ : Top.prod X Y ⟶ Top.prod X (Y ⊔ Z) :=
Top.mk_hom (λ p, (p.1, inY p.2)) (by continuity)

def XxZ_XYZ : Top.prod X Z ⟶ Top.prod X (Y ⊔ Z) :=
Top.mk_hom (λ p, (p.1, inZ p.2)) (by continuity)

def coprod : Is_coproduct XxY_XYZ XxZ_XYZ :=
Is_coproduct_of_Is_pushout_of_Is_initial po' Top.empty_is_initial_object

end
end distrib_private

def Top.prod.distrib {X Y Z : Top} :
  homeomorphism (Top.prod X Y ⊔ Top.prod X Z) (Top.prod X (Y ⊔ Z)) :=
isomorphic_coprod_of_Is_coproduct distrib_private.coprod

-- TODO: The above construction lost computational control of the
-- inverse morphism. We know it must be given by sending (x, inl y) to
-- inl (x, y) and similarly for Z. We could replace the inverse
-- morphism in prod.distrib; or possibly it would have been easier
-- from the start to just show that this formula defines a continuous
-- inverse.

end homotopy_theory.topological_spaces
