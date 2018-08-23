import category_theory.colimit_lemmas
import homotopy_theory.formal.cofibrations.cofibration_category
import homotopy_theory.formal.cofibrations.cylinder
import homotopy_theory.formal.cofibrations.factorization_from_cylinder
import .cylinder_object
import .dold

universes u v

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder
open homotopy_theory.weak_equivalences
open precofibration_category

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
  (assume a, ⟨I.obj a, ii @> a, p @> a, cof_ii a, heq_p, pii⟩)
  (assume x, ⟨x, 𝟙 x, ⟨cof_id x, weq_id x⟩, all_objects_fibrant x⟩)

-- The functor I produces cylinder objects in the general sense of
-- cofibration categories.
def canonical_cylinder (b : C) :
  relative_cylinder (all_objects_cofibrant.cofibrant.{u v} b) :=
⟨I.obj b,
 (pushout_by_cof (!b) (!b) _).is_pushout.induced (i 0 @> b) (i 1 @> b)
   (category_theory.initial.uniqueness _ _),
 p @> b,
 -- We proved ii : b ⊔ b → Ib is a cofibration; need to massage this
 -- into a map from the pushout over the initial object.
 let po := pushout_by_cof (!b) (!b) (all_objects_cofibrant.cofibrant.{u v} b),
     -- The map we need to show is a cofibration
     ii' := po.is_pushout.induced (i 0 @> b) (i 1 @> b)
       (category_theory.initial.uniqueness _ _),
     c : Is_coproduct po.map₀ po.map₁ :=
       Is_coproduct_of_Is_pushout_of_Is_initial po.is_pushout
         (has_initial_object.initial_object.{u v} C).is_initial_object,
     j : iso (b ⊔ b) po.ob := isomorphic_coprod_of_Is_coproduct c in
 have ii' ∘ j.hom = ii @> b, begin
   dsimp [j, isomorphic_coprod_of_Is_coproduct];
   apply coprod.uniqueness; rw ←assoc; simp [ii]
 end,
 have ii' = ii @> b ∘ j.inv, by rw ←this; simp,
 show is_cof ii',
 by rw this; exact cof_comp (cof_iso j.symm) (cof_ii b),
 heq_p,
 begin
   apply (pushout_by_cof (!b) (!b) _).is_pushout.uniqueness;
   { rw ←assoc, simp }
 end⟩

-- TODO: Relative cylinders?

-- TODO: Also verify that the I-category notion of homotopy matches
-- the cofibration category one?

end homotopy_theory.cofibrations
