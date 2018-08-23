import category_theory.isomorphism
import for_mathlib

import .category
import .subspace

open set

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}

-- TODO: Replace this @[reducible] with coercion to fun?
@[reducible] def homeomorphism (X Y : Top) := iso X Y

@[refl] def homeomorphism.refl (X : Top) : homeomorphism X X := iso.refl X

@[trans] def homeomorphism.trans {X Y Z : Top}
  (h₁ : homeomorphism X Y) (h₂ : homeomorphism Y Z) :
  homeomorphism X Z :=
h₁.trans h₂

def homeomorphism.of_equiv {X Y : Top} (h : X ≃ Y)
  (hf : continuous h) (hg : continuous h.symm) : homeomorphism X Y :=
{ hom := Top.mk_hom h hf,
  inv := Top.mk_hom h.symm hg,
  hom_inv_id := by ext p; change h.symm (h p) = p; simp,
  inv_hom_id := by ext p; change h (h.symm p) = p; simp }

variables {X Y Z : Top} (h : homeomorphism X Y)

-- TODO: Could also express this via forgetful functor, iso = ≃ for Set
def homeomorphism.equiv : X ≃ Y :=
{ to_fun := h,
  inv_fun := h.inv,
  left_inv := λ x, Top.hom_congr h.hom_inv_id x,
  right_inv := λ y, Top.hom_congr h.inv_hom_id y }

-- TODO: We could also use this to prove is_open_iff
lemma homeomorphism.embedding : embedding h :=
embedding_of_embedding_comp h.inv
  (by convert embedding_id; change function.comp h.equiv.symm h.equiv = id; simp)

lemma homeomorphism.is_open_iff (s : set Y) : is_open s ↔ is_open (h ⁻¹' s) :=
iff.intro (h.hom.property s) $
  have is_open (h ⁻¹' s) → is_open (h.equiv.symm ⁻¹' (h.equiv ⁻¹' s)), from
    h.inv.property _,
  begin
    intro H,
    convert this H,
    rw ←set.preimage_comp,
    simp [set.preimage_id]
  end

lemma homeomorphism.is_closed_iff (s : set Y) : is_closed s ↔ is_closed (h ⁻¹' s) :=
by rw [is_closed, is_closed, h.is_open_iff, set.preimage_compl]

-- TODO: maybe this actually belongs in `subspace`?
def homeomorphism.restrict {s : set X} {t : set Y} (hst : s = h ⁻¹' t) :
  homeomorphism (Top.mk_ob s) (Top.mk_ob t) :=
{ hom := Top.mk_hom (λ p, ⟨h p.val, by simpa [hst] using p.property⟩)
    (by have := h.hom.property; continuity),
  inv := Top.mk_hom (λ p, ⟨h.symm p.val, begin
      subst s, show h.equiv (h.equiv.symm p.val) ∈ t, simpa using p.property
    end⟩)
    (by have := h.inv.property; continuity),
  hom_inv_id := by ext p; exact h.equiv.left_inv p.val,
  inv_hom_id := by ext p; exact h.equiv.right_inv p.val }

lemma homeomorphism.restriction_commutes {s : set X} {t : set Y} (hst : s = h ⁻¹' t) :
  incl t ∘ (h.restrict hst).hom = h.hom ∘ incl s :=
by ext; refl

-- Better than h ▸ refl because this lets the val field compute.
def subspace_equiv_subspace {X : Top} {A A' : set X} (h : A = A') :
  homeomorphism (Top.mk_ob A) (Top.mk_ob A') :=
(homeomorphism.refl X).restrict h

-- This definition cannot be computable because the information that a
-- point of X lies in the range of j is stored in a Prop, and so is
-- unavailable at runtime.

-- Hopefully it's okay to use let inside a definition like this
noncomputable def homeomorphism_to_image_of_embedding {A X : Top} {j : A ⟶ X}
  (h : embedding j) : homeomorphism A (Top.mk_ob (range j)) :=
let j' := Top.factor_through_incl j (range j) (subset.refl _),
    e := (equiv.set.range j h.1).replace_to_fun j' (by funext p; simp; refl) in
homeomorphism.of_equiv e j'.property
  (continuous_of_embedding_of_continuous_comp h $ begin
    convert continuous_subtype_val using 1, funext p,
    exact congr_arg subtype.val (e.right_inv p)
  end)

-- TODO: Would also be action on isomorphisms of the functor X × -
def homeomorphism.prod_congr_right (h : homeomorphism Y Z) :
  homeomorphism (Top.prod X Y) (Top.prod X Z) :=
{ hom := Top.prod_maps (𝟙 X) h,
  inv := Top.prod_maps (𝟙 X) h.symm,
  hom_inv_id := begin
    ext pq, { refl },
    { cases pq with p q,
      change h.equiv.symm (h.equiv q) = q, simp }
  end,
  inv_hom_id := begin
    ext pr, { refl },
    { cases pr with p r,
      change h.equiv (h.equiv.symm r) = r, simp }
  end }

def prod_singleton (h : * ≃ Y) : homeomorphism X (Top.prod X Y) :=
{ hom := Top.prod_pt (h punit.star),
  inv := Top.pr₁,
  hom_inv_id := by ext; refl,
  inv_hom_id := begin
    ext p, { refl },
    { rcases p with ⟨x, y⟩,
      convert h.right_inv y, change h punit.star = h (h.symm y),
      cases h.symm y, refl }
  end }

def prod_comm {X Y : Top} : homeomorphism (Top.prod X Y) (Top.prod Y X) :=
{ hom := Top.mk_hom (λ p, (p.2, p.1)) (by continuity),
  inv := Top.mk_hom (λ p, (p.2, p.1)) (by continuity),
  hom_inv_id := by ext xy; cases xy; refl,
  inv_hom_id := by ext xy; cases xy; refl }

def prod_assoc {X Y Z : Top} : homeomorphism (Top.prod (Top.prod X Y) Z) (Top.prod X (Top.prod Y Z)) :=
{ hom := Top.mk_hom (λ p, (p.1.1, (p.1.2, p.2))) (by continuity),
  inv := Top.mk_hom (λ p, ((p.1, p.2.1), p.2.2)) (by continuity),
  hom_inv_id := by ext xyz; rcases xyz with ⟨⟨x, y⟩, z⟩; refl,
  inv_hom_id := by ext xyz; rcases xyz with ⟨x, ⟨y, z⟩⟩; refl }

end «Top»
end homotopy_theory.topological_spaces
