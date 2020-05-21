import category_theory.bundled
import category_theory.induced
import homotopy_theory.formal.cofibrations.track
import homotopy_theory.formal.i_category.cofibration_category
import .pi_n

noncomputable theory

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open Top
local notation `Top` := Top.{0}

def Pi₁_ (X : Top) : Type := X

instance {X : Top} : groupoid (Pi₁_ X) :=
show groupoid
  (induced_category
    (homotopy_class_groupoid
      (all_objects_cofibrant.cofibrant Top.point)
      (canonical_cylinder.{0 1} Top.point)
      (all_objects_fibrant X))
    (λ x, (Top.const x : Top.point ⟶ X))),
by apply_instance

def Pi₁_induced {X Y : Top} (f : X ⟶ Y) : Pi₁_ X ↝ Pi₁_ Y :=
induced_functor' _ _
  (homotopy_class_functor (all_objects_fibrant X) (all_objects_fibrant Y) f)
  f
  (by intros; refl)

def Pi₁ : Top ↝ Gpd :=
{ obj := λ X, Gpd.mk_ob (Pi₁_ X),
  map := λ X Y f, Gpd.mk_hom (Pi₁_induced f),
  map_id' := λ X, begin
    dsimp [Pi₁_induced], simp only [homotopy_class_functor.map_id],
    apply induced_functor_id
  end,
  map_comp' := λ X Y Z f g, begin
    dsimp [Gpd.mk_hom, Pi₁_induced, induced_functor, Gpd.category],
    have : ∀ W : Top, fibrant W := all_objects_fibrant,
    simp only [homotopy_class_functor.map_comp
      (all_objects_fibrant X) (all_objects_fibrant Y) _
      (all_objects_fibrant Z)],
    apply induced_functor_comp
  end }

end homotopy_theory.topological_spaces
