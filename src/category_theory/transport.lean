import category_theory.base
import category_theory.functor
import category_theory.groupoid
import data.equiv.basic

-- Transport category/groupoid structures along an isomorphism of
-- graphs (with same objects).

universes v v' u x x' w

namespace category_theory
open category functor groupoid

variables {C : Type u}

section category
variables (cat : category.{v} C)
variables {hom' : Π a b : C, Type v'} (e : Π a b : C, hom a b ≃ hom' a b)

def transported_category : category.{v'} C :=
{ hom := hom',
  id := λ a, e a a (id a),
  comp := λ a b c f g, e a c (comp ((e a b).symm f) ((e b c).symm g)),
  id_comp' := by intros; simp,
  comp_id' := by intros; simp,
  assoc' := by intros; simp }

end category

section groupoid
variables (gpd : groupoid.{v} C)
variables {hom' : Π a b : C, Type v'} (e : Π a b : C, hom a b ≃ hom' a b)

def transported_groupoid : groupoid.{v'} C :=
{ inv := λ a b f, e b a (groupoid.inv ((e a b).symm f)),
  inv_comp' := by intros; dsimp [transported_category]; simp,
  comp_inv' := by intros; dsimp [transported_category]; simp,
  .. transported_category gpd.to_category e }

end groupoid

section functor
-- Many possible setups; this is the one we need.
variables [catC : category.{v} C]
variables {D : Type w} [catD : category.{x} D]
variables {hom'C : Π a b : C, Type v'} (eC : Π a b : C, hom a b ≃ hom'C a b)
variables {hom'D : Π a b : D, Type x'} (eD : Π a b : D, hom a b ≃ hom'D a b)
variables (F : C ↝ D)

def transported_functor :
  @functor C (transported_category catC eC) D (transported_category catD eD) :=
{ obj := F.obj,
  map := λ a b f, eD (F.obj a) (F.obj b) (F &> (eC a b).symm f),
  map_id' := by intros; dsimp [transported_category]; simp; refl,
  map_comp' := by intros; dsimp [transported_category]; simp; refl }

end functor

end category_theory
