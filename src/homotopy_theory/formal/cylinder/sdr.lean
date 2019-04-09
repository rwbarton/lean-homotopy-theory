import .homotopy

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cylinder

variables {C : Type u} [cat : category.{v+1} C] [has_cylinder C]
include cat

-- A map j : A → X is the inclusion of a strong deformation retract if
-- it admits a retraction r : X → A for which j ∘ r is homotopic to
-- the identity rel j.
structure sdr_inclusion {a x : C} (j : a ⟶ x) :=
(r : x ⟶ a)
(h : r ∘ j = 𝟙 a)
(H : j ∘ r ≃ 𝟙 x rel j)

def is_sdr_inclusion {a x : C} (j : a ⟶ x) : Prop := nonempty (sdr_inclusion j)

lemma pushout_of_sdr_inclusion {a x a' x' : C} {j : a ⟶ x} {f : a ⟶ a'} {f' : x ⟶ x'}
  {j' : a' ⟶ x'} (po : Is_pushout j f f' j')
  (po' : Is_pushout (I &> j) (I &> f) (I &> f') (I &> j')) :
  is_sdr_inclusion j → is_sdr_inclusion j' :=
assume ⟨⟨r, h, ⟨H, Hrel⟩⟩⟩, begin
  refine ⟨⟨po.induced (f ∘ r) (𝟙 a') (by rw [←assoc, h]; simp), by simp, _⟩⟩,
  -- Now need to give a homotopy from j' ∘ r' (r' = the above induced
  -- map) to 𝟙 x', rel j'. We define the homotopy using H on I +> x,
  -- and the constant homotopy at the identity on I +> a'.
  refine ⟨⟨po'.induced (f' ∘ H.H) (j' ∘ p @> a') _, _, _⟩, _⟩,
  -- The above maps agree on I +> a, so we can form the induced map:
  { unfold homotopy.is_rel at Hrel, rw [←assoc, Hrel, p_nat_assoc],
    have : f' ∘ (j ∘ r ∘ j ∘ p @> a) = (f' ∘ j) ∘ (r ∘ j) ∘ p @> a, by simp,
    rw [this, po.commutes, h], dsimp, simp },
  -- The homotopy defined in this way starts at j' ∘ r' : x' → x':
  { apply po.uniqueness; rw i_nat_assoc; conv { to_rhs, rw ←assoc }; simp;
      rw ←assoc,
    { erw [H.Hi₀, assoc, po.commutes] },
    { rw [pi_components], simp } },
  -- ... and ends at 𝟙 x':
  { apply po.uniqueness; rw i_nat_assoc; simp; rw [←assoc],
    { erw H.Hi₁; simp }, { rw [pi_components], simp } },
  -- ... and is rel j:
  { unfold homotopy.is_rel,
    simp, congr, rw [←assoc], dsimp, simp }
end

end homotopy_theory.cylinder
