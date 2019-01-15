import homotopy_theory.formal.i_category.definitions

import .precofibration_category

noncomputable theory

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open homotopy_theory.cofibrations.precofibration_category
open homotopy_theory.cylinder

-- Top is an I-category with cofibrations the closed cofibrations and
-- cylinder functor - × [0, 1].
instance : I_category.{0 1} Top :=
{ I_preserves_pushout_by_cof := λ _ _ _ _ _ _ _ _ _ po,
    preserves_pushouts.Is_pushout_of_Is_pushout I po,
  hep_cof := assume a b j hj, two_sided_hep_iff_hep.mpr hj.1,
  relative_cylinder := assume a b j hj,
    let po := pushout_by_cof (∂I &> j) (ii @> a) (cof_coprod hj hj) in
    show is_cof (po.is_pushout.induced (ii @> b) (I &> j) (ii.naturality _)), from
    let ⟨po', h⟩ := relative_cylinder' j hj.2 hj.1 in
    by convert cof_comp (cof_iso (pushout.unique po.is_pushout po'.is_pushout)) h;
       apply po.is_pushout.uniqueness; rw ←assoc; simp }

end homotopy_theory.topological_spaces
