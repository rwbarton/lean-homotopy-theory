import homotopy_theory.formal.cofibrations.precofibration_category
import homotopy_theory.formal.cylinder.definitions
import homotopy_theory.formal.cylinder.hep
import homotopy_theory.formal.weak_equivalences.definitions

universes v u

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder

/-

An I-category [Baues, Algebraic homotopy, §I.3] is a precofibration
category C equipped with a cylinder functor satisfying the following
additional axioms.

* C has an initial object and every object of C is cofibrant.

  From the axioms of a precofibration category, it follows that C
  admits coproducts. Because we will need these coproducts in order to
  state a later axiom, we assume that C already comes equipped with a
  choice of coproducts in order to avoid non-definitionally equal
  instances.

* The cylinder functor I preserves pushouts by cofibrations and the
  initial object.

* Cofibrations have the two-sided HEP with respect to the cylinder I.

* The relative cylinder axiom: using the notation ∂I A = A ⊔ A, for
  each cofibration A → X, in the square

    ∂I A → I A
      ↓     ↓
    ∂I X → I X,

  the induced map from the pushout to I X is again a cofibration. (The
  pushout exists because ∂I A → ∂I X is a cofibration.)

* The cylinder I is equipped with an interchange structure.

-/

variables (C : Type u) [category.{v} C] [has_initial_object.{v} C] [has_coproducts.{v} C]

class I_category extends has_cylinder C, preserves_initial_object (I : C ↝ C),
  precofibration_category C, all_objects_cofibrant.{v} C,
  cylinder_has_interchange.{v} C :=
(I_preserves_pushout_by_cof :
  Π {a b a' b'} {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
  is_cof f → Is_pushout f g g' f' → Is_pushout (I &> f) (I &> g) (I &> g') (I &> f'))
(hep_cof : ∀ {a b} (j : a ⟶ b), is_cof j → two_sided_hep j)
(relative_cylinder : ∀ {a b} (j : a ⟶ b) (hj : is_cof j), is_cof $
  (pushout_by_cof (∂I &> j) (ii @> a) (cof_coprod hj hj)).is_pushout.induced
    (ii @> b) (I &> j) (ii.naturality _))

open precofibration_category
open I_category
variables {C}

-- Alternate formulation of the relative cylinder axiom, using an
-- arbitrary pushout rather than the one given by the precofibration
-- category structure.
lemma relative_cylinder' [I_category.{v} C] {a b : C} (j : a ⟶ b) (hj : is_cof j)
  {z} (ii' : ∂I.obj b ⟶ z) (jj' : I.obj a ⟶ z) (po : Is_pushout (∂I &> j) (ii @> a) ii' jj') :
  is_cof (po.induced (ii @> b) (I &> j) (ii.naturality _)) :=
let po' := (pushout_by_cof (∂I &> j) (ii @> a) (cof_coprod hj hj)).is_pushout in
by convert cof_comp (cof_iso (pushout.unique po po')) (relative_cylinder j hj);
   apply po.uniqueness; rw ←category.assoc; simp; refl

end homotopy_theory.cofibrations
