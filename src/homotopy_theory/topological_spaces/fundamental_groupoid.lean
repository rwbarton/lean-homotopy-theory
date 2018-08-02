import homotopy_theory.formal.cofibrations.track
import homotopy_theory.formal.i_category.cofibration_category
import .pi_n

noncomputable theory

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open Top
local notation `Top` := Top.{0}

def Pi₁ (X : Top) : Type :=
homotopy_class_groupoid
  (all_objects_cofibrant.cofibrant Top.point)
  (canonical_cylinder.{1 0} Top.point)
  (all_objects_fibrant X)

instance {X : Top} : groupoid (Pi₁ X) := by unfold Pi₁; apply_instance

end homotopy_theory.topological_spaces
