import homotopy_theory.formal.cofibrations.cofibration_category
import homotopy_theory.formal.cofibrations.factorization_from_cylinder
import .cylinder_object
import .dold

universes u v

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder
open homotopy_theory.weak_equivalences

-- An I-category gives rise to a cofibration category with the same
-- cofibrations in which the weak equivalences are the homotopy
-- equivalences.

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C]
  [I_category.{u v} C]
include cat

-- Every object is fibrant.
lemma all_objects_fibrant (x : C) : fibrant x :=
assume y j ⟨jc, jw⟩,
let ⟨⟨r, h, H⟩⟩ := (heq_iff_sdr_inclusion jc).mp jw in ⟨r, h⟩

instance I_category.cofibration_category : cofibration_category.{u v} C :=
cofibration_category.mk_from_cylinder
  (assume a b a' b' f g f' g' po ⟨fc, fw⟩,
    ⟨precofibration_category.pushout_is_cof po fc, pushout_is_acof po fc fw⟩)
  (assume a, ⟨I +> a, ii @> a, p @> a, cof_ii a, heq_p, pii⟩)
  (assume x, ⟨x, 𝟙 x, ⟨cof_id x, weq_id x⟩, all_objects_fibrant x⟩)

end homotopy_theory.cofibrations
