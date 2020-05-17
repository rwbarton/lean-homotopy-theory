import category_theory.base
import category_theory.eq_to_hom
import category_theory.groupoid
import category_theory.full_subcategory

universes v x z u u' w w' y y'

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace category_theory

variables {C : Type u} {C' : Type u'} (k : C' → C)

-- TODO: merge with category_theory.full_subcategory

local attribute [simps] induced_category.category

def induced_groupoid (gpd : groupoid.{v} C) : groupoid.{v} C' :=
{ inv := λ X Y f, groupoid.inv f,
  .. induced_category.category k }

instance induced_category.groupoid [i : groupoid.{v} C] : groupoid.{v} (induced_category C k) :=
induced_groupoid k i

variables {D : Type w} {D' : Type w'} (l : D' → D)

def induced_functor' {catC : category.{v} C} {catD : category.{x} D} (F : C ↝ D)
  (F' : C' → D') (e : ∀ a, F.obj (k a) = l (F' a)) :
  induced_category C k ↝ induced_category D l :=
{ obj := F',
  map := λ X Y f,
    show l (F' X) ⟶ l (F' Y), from
    eq_to_hom (e Y) ∘ (F &> f) ∘ eq_to_hom (e X).symm,
  map_id' := λ X, by dsimp; rw F.map_id; simp,
  map_comp' := λ X Y Z f g, by dsimp; rw F.map_comp; simp }

lemma induced_functor_id [catC : category.{v} C] :
  induced_functor' k k (functor.id C) id (λ a, rfl) =
  functor.id (induced_category C k) :=
begin
  fapply functor.ext,
  { intro a, refl },
  { intros a b f, dsimp [induced_functor'], simp }
end

variables {E : Type y} {E' : Type y'} (m : E' → E)
lemma induced_functor_comp [catC : category.{v} C]
  [catD : category.{x} D] [catE : category.{z} E]
  {F : C ↝ D} {F' : C' → D'} (eF : ∀ a, F.obj (k a) = l (F' a))
  {G : D ↝ E} {G' : D' → E'} (eG : ∀ a, G.obj (l a) = m (G' a)) :
  induced_functor' k m (F.comp G) (function.comp G' F')
    (by intro a; change G.obj (F.obj (k a)) = _; rw [eF, eG]) =
    induced_functor' k l F F' eF ⋙ induced_functor' l m G G' eG :=
begin
  fapply functor.ext,
  { intro a, refl },
  { intros a b f,
    -- This proof mysteriously broke
    dsimp [induced_functor'],
    rw category.id_comp,
    erw category.comp_id,
    -- FIXME: Why was this lemma removed from simp?
    simp [eq_to_hom_map], refl }
end

end category_theory
