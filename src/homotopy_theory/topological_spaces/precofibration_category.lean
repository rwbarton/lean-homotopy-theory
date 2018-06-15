import homotopy_theory.formal.cofibrations.precofibration_category
import homotopy_theory.formal.cylinder.hep

import .cofibrations
import .colimits
import .pushout_lemmas

open set

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open homotopy_theory.cylinder
open Top
local notation `Top` := Top.{0}

-- We're interested in structures whose "cofibrations" are the
-- *closed* cofibrations, that is, the cofibrations in the classical
-- sense with closed image.
def closed_cofibration {A X : Top} (j : A ⟶ X) : Prop :=
cofibration j ∧ is_closed (range j)

lemma closed_cofibration.is_closed {A X : Top} {j : A ⟶ X} (hj : closed_cofibration j)
  {v : set A} : is_closed v → is_closed (j '' v) :=
embedding_is_closed (embedding_of_cofibration hj.1) hj.2

lemma closed_cofibration_id (A : Top) : closed_cofibration (𝟙 A) :=
⟨hep_id 0,
 by change is_closed (range (id : A → A)); rw [range_id]; exact is_closed_univ⟩

lemma closed_cofibration_comp {A B C : Top} {j : A ⟶ B} {k : B ⟶ C}
  (hj : closed_cofibration j) (hk : closed_cofibration k) :
  closed_cofibration (k ∘ j) :=
⟨hep_comp 0 hj.1 hk.1,
 by change is_closed (range (function.comp k j)); rw [range_comp];
    exact hk.is_closed hj.2⟩

instance : precofibration_category Top :=
{ is_cof := @closed_cofibration,
  mem_id := closed_cofibration_id,
  mem_comp := @closed_cofibration_comp,
  pushout_by_cof := λ _ _ _ f g _, has_pushouts.pushout f g,
  pushout_is_cof := λ _ _ _ _ f g f' g' po ⟨co_f, cl_f⟩,
    ⟨hep_pushout' 0 po co_f, (range_i_closed_iff_range_j_closed po).mp cl_f⟩ }

end homotopy_theory.topological_spaces
