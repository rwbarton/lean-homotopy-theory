import categories.isomorphism
import for_mathlib

import .category
import .subspace

open categories.isomorphism

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}

-- TODO: Replace this @[reducible] with coercion to fun?
@[reducible] def homeomorphism (X Y : Top) := Isomorphism X Y

@[trans] def homeomorphism.trans {X Y Z : Top}
  (h₁ : homeomorphism X Y) (h₂ : homeomorphism Y Z) :
  homeomorphism X Z :=
h₁.trans h₂

variables {X Y : Top} (h : homeomorphism X Y)

def homeomorphism.equiv : X ≃ Y :=
{ to_fun := h,
  inv_fun := h.inverse,
  left_inv := λ x, Top.hom_congr h.witness_1 x,
  right_inv := λ y, Top.hom_congr h.witness_2 y }

-- TODO: We could also use this to prove is_open_iff
lemma homeomorphism.embedding : embedding h :=
embedding_of_embedding_comp h.symm.morphism
  (by convert embedding_id; change h.equiv.symm ∘ h.equiv = id; simp)

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
  incl t ∘ h.restrict hst = h ∘ incl s :=
by ext; refl

end «Top»
end homotopy_theory.topological_spaces
