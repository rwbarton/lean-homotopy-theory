import category_theory.isomorphism

import .category
import .colimits
import .cylinder
import .distrib
import .homeomorphism

noncomputable theory

open set

open category_theory (hiding embedding)

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{0}

-- The set of endpoints of the unit interval, as a space.
def I01_endpoints : Top := Top.mk_ob ({0, 1} : set I01)
instance I01_endpoints.has_zero : has_zero I01_endpoints := ⟨⟨0, by simp⟩⟩
instance I01_endpoints.has_one : has_one I01_endpoints := ⟨⟨1, by simp⟩⟩

instance Top.point.discrete_space : discrete_space Top.point :=
{ to_topological_space := ⊥,
  is_discrete_topology :=
    discrete_iff_singletons_open.mpr
      (λ ⟨⟩, by convert is_open_univ; ext p; cases p; simp) }

def two_endpoints : homeomorphism (* ⊔ *) I01_endpoints :=
let j : * ⊔ * ⟶ I01 :=
  coprod.induced
    (Top.mk_hom (λ _, 0) (by continuity))
    (Top.mk_hom (λ _, 1) (by continuity)) in
have rj : range j = {0, 1}, begin
  ext p, split,
  { intro h, rcases h with ⟨⟨⟨⟩⟩|⟨⟨⟩⟩, rfl⟩,
    { change (0 : I01) ∈ _, simp }, { change (1 : I01) ∈ _, simp } },
  { intro h, have : p = 1 ∨ p = 0, by simp at h; exact h,
    cases this,
    { subst this, exact ⟨sum.inr punit.star, rfl⟩ },
    { subst this, exact ⟨sum.inl punit.star, rfl⟩ } }
end,
have function.injective j, begin
  intros a b h, rcases a with ⟨⟨⟩⟩|⟨⟨⟩⟩; rcases b with ⟨⟨⟩⟩|⟨⟨⟩⟩,
  any_goals { refl },
  { change (0 : I01) = 1 at h,
    have h' : (0 : ℝ) = 1 := congr_arg subtype.val h,
    simpa using h' },
  { change (1 : I01) = 0 at h,
    have h' : (1 : ℝ) = 0 := congr_arg subtype.val h,
    simpa using h' }
end,
have embedding j, begin
  refine ⟨this, _⟩,
  have : Top.topological_space (* ⊔ *) = ⊤,
    from @is_discrete_topology (* ⊕ *) _,
  change sum.topological_space = _,
  transitivity ⊤,
  exact sum.discrete_space.is_discrete_topology,
  symmetry,
  apply discrete_iff_singletons_open.mpr, intro e,
  rcases e with ⟨⟨⟩⟩|⟨⟨⟩⟩,
  { refine ⟨{t : I01 | t.val < 1},
      is_open_lt continuous_subtype_val continuous_const, _⟩,
    ext p, split,
    { intro h, simp at h, subst p, change (0 : ℝ) < 1, norm_num },
    { intro h, rcases p with ⟨⟨⟩⟩|⟨⟨⟩⟩, { simp },
      { change (1 : ℝ) < 1 at h, have : ¬((1 : ℝ) < 1), by norm_num,
        contradiction } } },
  { refine ⟨{t : I01 | t.val > 0},
      is_open_lt continuous_const continuous_subtype_val, _⟩,
    ext p, split,
    { intro h, simp at h, subst p, change (1 : ℝ) > 0, norm_num },
    { intro h, rcases p with ⟨⟨⟩⟩|⟨⟨⟩⟩,
      { change (0 : ℝ) > 0 at h, have : ¬((0 : ℝ) > 0), by norm_num,
        contradiction },
      { simp } } }
end,
(homeomorphism_to_image_of_embedding this).trans
  (subspace_equiv_subspace rj)

def prod_doubleton {X : Top} : homeomorphism (∂I.obj X) (Top.prod X I01_endpoints) :=
calc
  ∂I.obj X
    ≅ ∂I.obj (Top.prod X Top.point)
    : (∂I).on_iso (prod_singleton (by refl))
... ≅ Top.prod X Top.point ⊔ Top.prod X Top.point
    : by refl
... ≅ Top.prod X (* ⊔ *)
    : Top.prod.distrib
... ≅ Top.prod X I01_endpoints
    : two_endpoints.prod_congr_right

end homotopy_theory.topological_spaces
