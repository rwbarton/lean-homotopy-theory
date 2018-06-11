import categories.isomorphism
import for_mathlib

import .category
import .subspace

open set

open categories.isomorphism
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}

-- TODO: Replace this @[reducible] with coercion to fun?
@[reducible] def homeomorphism (X Y : Top) := Isomorphism X Y

@[refl] def homeomorphism.refl (X : Top) : homeomorphism X X := Isomorphism.refl X

@[trans] def homeomorphism.trans {X Y Z : Top}
  (h₁ : homeomorphism X Y) (h₂ : homeomorphism Y Z) :
  homeomorphism X Z :=
h₁.trans h₂

def homeomorphism.of_equiv {X Y : Top} (h : X ≃ Y)
  (hf : continuous h) (hg : continuous h.symm) : homeomorphism X Y :=
{ morphism := Top.mk_hom h hf,
  inverse := Top.mk_hom h.symm hg,
  witness_1 := by ext p; change h.symm (h p) = p; simp,
  witness_2 := by ext p; change h (h.symm p) = p; simp }

variables {X Y : Top} (h : homeomorphism X Y)

def homeomorphism.equiv : X ≃ Y :=
{ to_fun := h,
  inv_fun := h.inverse,
  left_inv := λ x, Top.hom_congr h.witness_1 x,
  right_inv := λ y, Top.hom_congr h.witness_2 y }

-- TODO: We could also use this to prove is_open_iff
lemma homeomorphism.embedding : embedding h :=
embedding_of_embedding_comp h.symm.morphism
  (by convert embedding_id; change function.comp h.equiv.symm h.equiv = id; simp)

lemma homeomorphism.is_open_iff (s : set Y) : is_open s ↔ is_open (h ⁻¹' s) :=
iff.intro (h.morphism.property s) $
  have is_open (h ⁻¹' s) → is_open (h.equiv.symm ⁻¹' (h.equiv ⁻¹' s)), from
    h.symm.morphism.property _,
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
{ morphism := Top.mk_hom (λ p, ⟨h p.val, by simpa [hst] using p.property⟩)
    (by have := h.morphism.property; continuity),
  inverse := Top.mk_hom (λ p, ⟨h.symm p.val, begin
      subst s, show h.equiv (h.equiv.symm p.val) ∈ t, simpa using p.property
    end⟩)
    (by have := h.symm.morphism.property; continuity),
  witness_1 := by ext p; exact subtype.eq (h.equiv.left_inv p.val),
  witness_2 := by ext p; exact subtype.eq (h.equiv.right_inv p.val) }

lemma homeomorphism.restriction_commutes {s : set X} {t : set Y} (hst : s = h ⁻¹' t) :
  incl t ∘ (h.restrict hst).morphism = h.morphism ∘ incl s :=
by ext; refl

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

def prod_singleton (h : * ≃ Y) : homeomorphism X (Top.prod X Y) :=
{ morphism := Top.prod_pt (h punit.star),
  inverse := Top.pr₁,
  witness_1 := by ext; refl,
  witness_2 := begin
    ext p, rcases p with ⟨x, y⟩, change (x, _) = (x, y), congr,
    convert h.right_inv y, change h punit.star = h (h.symm y),
    cases h.symm y, refl
  end }

def prod_comm {X Y : Top} : homeomorphism (Top.prod X Y) (Top.prod Y X) :=
{ morphism := Top.mk_hom (λ p, (p.2, p.1)) (by continuity),
  inverse := Top.mk_hom (λ p, (p.2, p.1)) (by continuity),
  witness_1 := by ext xy; cases xy; refl,
  witness_2 := by ext xy; cases xy; refl }

def prod_assoc {X Y Z : Top} : homeomorphism (Top.prod (Top.prod X Y) Z) (Top.prod X (Top.prod Y Z)) :=
{ morphism := Top.mk_hom (λ p, (p.1.1, (p.1.2, p.2))) (by continuity),
  inverse := Top.mk_hom (λ p, ((p.1, p.2.1), p.2.2)) (by continuity),
  witness_1 := by ext xyz; rcases xyz with ⟨⟨x, y⟩, z⟩; refl,
  witness_2 := by ext xyz; rcases xyz with ⟨x, ⟨y, z⟩⟩; refl }

end «Top»
end homotopy_theory.topological_spaces
