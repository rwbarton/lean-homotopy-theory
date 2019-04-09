import category_theory.base
import category_theory.eq_to_hom
import category_theory.groupoid

universes v x z u u' w w' y y'

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace category_theory

variables {C : Type u} {C' : Type u'} (k : C' → C)

-- TODO: reconcile with category_theory.full_subcategory

def induced_category' (cat : category.{v} C) : category.{v} C' :=
{ hom := λ X Y, k X ⟶ k Y,
  id := λ X, 𝟙 (k X),
  comp := λ _ _ _ f g, f ≫ g }

def induced_groupoid (gpd : groupoid.{v} C) : groupoid.{v} C' :=
{ inv := λ X Y f, groupoid.inv f,
  inv_comp' := by dsimp [induced_category']; simp,
  comp_inv' := by dsimp [induced_category']; simp,
  .. induced_category' k gpd.to_category }

variables {D : Type w} {D' : Type w'} (l : D' → D)

def induced_functor' [catC : category.{v} C] [catD : category.{x} D] (F : C ↝ D)
  (F' : C' → D') (e : ∀ a, F.obj (k a) = l (F' a)) :
  @functor C' (induced_category' k catC) D' (induced_category' l catD) :=
{ obj := F',
  map := λ X Y f,
    show l (F' X) ⟶ l (F' Y), from
    eq_to_hom (e Y) ∘ (F &> f) ∘ eq_to_hom (e X).symm,
  map_id' := λ X, by dsimp [induced_category']; rw F.map_id; simp,
  map_comp' := λ X Y Z f g, by dsimp [induced_category']; rw F.map_comp; simp }

def induced_functor_gpd [gpdC : groupoid.{v} C] [gpdD : groupoid.{x} D] (F : C ↝ D)
  (F' : C' → D') (e : ∀ a, F.obj (k a) = l (F' a)) :
  @functor C' (induced_groupoid k gpdC).to_category D' (induced_groupoid l gpdD).to_category :=
induced_functor' k l F F' e

lemma induced_functor_id [catC : category.{v} C] :
  induced_functor' k k (functor.id C) id (λ a, rfl) =
  @functor.id C' (induced_category' k catC) :=
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
  @functor.comp
    C' (induced_category' k catC)
    D' (induced_category' l catD)
    E' (induced_category' m catE)
    (induced_functor' k l F F' eF) (induced_functor' l m G G' eG) :=
begin
  fapply functor.ext,
  { intro a, refl },
  { intros a b f,
    -- This proof mysteriously broke
    dsimp [induced_functor'],
    rw category.id_comp,
    erw category.comp_id,
    simp, refl }
end

end category_theory
