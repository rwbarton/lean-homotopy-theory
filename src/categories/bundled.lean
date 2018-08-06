import categories.eq
import categories.functor
import categories.groupoid

universe u

-- The category of categories and the category of groupoids.

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace categories
open categories.functor

-- TODO: Deduplicate
infixr ` &> `:85 := functor.Functor.onMorphisms

section Cat

structure Cat : Type (u+1) :=
(carrier : Type u)
(cat : category.{u u} carrier)

local notation `Cat` := Cat.{u}

instance Cat.to_sort : has_coe_to_sort Cat :=
{ S := Type u, coe := λ X, X.carrier }

instance Cat.as_category (C : Cat) : category.{u u} C.carrier := C.cat

def Cat.functor (C D : Cat) : Type u := C ↝ D

instance Cat.category : category Cat :=
{ Hom := Cat.functor,
  identity := λ C, IdentityFunctor C,
  compose := λ _ _ _ F G, FunctorComposition F G,
  left_identity := λ _ _ F, by cases F; refl,
  right_identity := λ _ _ F, by cases F; refl }

end «Cat»


section Gpd

structure Gpd : Type (u+1) :=
(carrier : Type u)
(gpd : groupoid.{u u} carrier)

local notation `Gpd` := Gpd.{u}

instance Gpd.to_sort : has_coe_to_sort Gpd :=
{ S := Type u, coe := λ X, X.carrier }

instance Gpd.as_groupoid (C : Gpd) : groupoid.{u u} C.carrier := C.gpd

def Gpd.functor (C D : Gpd) : Type u := C ↝ D

instance Gpd.category : category Gpd :=
{ Hom := Gpd.functor,
  identity := λ C, IdentityFunctor C,
  compose := λ _ _ _ F G, FunctorComposition F G,
  left_identity := λ _ _ F, by cases F; refl,
  right_identity := λ _ _ F, by cases F; refl }

def Gpd.mk_ob (α : Type u) [gpd : groupoid α] : Gpd := ⟨α, gpd⟩
def Gpd.mk_hom {C D : Gpd} (f : C ↝ D) : C ⟶ D := f

end «Gpd»

end categories
