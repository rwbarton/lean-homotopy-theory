import categories.category
import categories.functor
import categories.groupoid

-- Transport category/groupoid structures along an isomorphism of
-- graphs (with same objects).

universes u v v'

namespace categories
open category categories.functor groupoid

variables {C : Type u}

section category
variables (cat : category.{u v} C)
variables {Hom' : Π a b : C, Type v'} (e : Π a b : C, Hom a b ≃ Hom' a b)

def transported_category : category.{u v'} C :=
{ Hom := Hom',
  identity := λ a, e a a (𝟙 a : Hom a a),
  compose := λ a b c f g, e a c (compose ((e a b).symm f) ((e b c).symm g)),
  left_identity := by intros; simp,
  right_identity := by intros; simp,
  associativity := by intros; simp }

end category

section groupoid
variables (gpd : groupoid.{u v} C)
variables {Hom' : Π a b : C, Type v'} (e : Π a b : C, Hom a b ≃ Hom' a b)

def transported_groupoid : groupoid.{u v'} C :=
{ inverse := λ a b f, e b a (groupoid.inverse ((e a b).symm f)),
  left_inverse := by intros; dsimp [transported_category]; simp,
  right_inverse := by intros; dsimp [transported_category]; simp,
  .. transported_category gpd.to_category e }

end groupoid

section functor
-- Many possible setups; this is the one we need.
universes w x x'
variables [catC : category.{u v} C]
variables {D : Type w} [catD : category.{w x} D]
variables {Hom'C : Π a b : C, Type v'} (eC : Π a b : C, Hom a b ≃ Hom'C a b)
variables {Hom'D : Π a b : D, Type x'} (eD : Π a b : D, Hom a b ≃ Hom'D a b)
variables (F : C ↝ D)

def transported_functor :
  @Functor C (transported_category catC eC) D (transported_category catD eD) :=
{ onObjects := F.onObjects,
  onMorphisms := λ a b f, eD (F +> a) (F +> b) (F &> (eC a b).symm f),
  identities := by intros; dsimp [transported_category]; simp,
  functoriality := by intros; dsimp [transported_category]; simp }

end functor

end categories
