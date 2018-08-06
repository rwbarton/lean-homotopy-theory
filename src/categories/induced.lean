import categories.eq
import categories.functor
import categories.groupoid

universes u u' v w w' x y y' z

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace categories

variables {C : Type u} {C' : Type u'} (k : C' → C)

def induced_category (cat : category.{u v} C) : category.{u' v} C' :=
{ Hom := λ X Y, k X ⟶ k Y,
  identity := λ X, 𝟙 (k X),
  compose := λ _ _ _ f g, f ≫ g }

def induced_groupoid (gpd : groupoid.{u v} C) : groupoid.{u' v} C' :=
{ inverse := λ X Y f, groupoid.inverse f,
  left_inverse := by dsimp [induced_category]; simp,
  right_inverse := by dsimp [induced_category]; simp,
  .. induced_category k gpd.to_category }

variables {D : Type w} {D' : Type w'} (l : D' → D)

def induced_functor [catC : category.{u v} C] [catD : category.{w x} D] (F : C ↝ D)
  (F' : C' → D') (e : ∀ a, F.onObjects (k a) = l (F' a)) :
  @functor.Functor C' (induced_category k catC) D' (induced_category l catD) :=
{ onObjects := F',
  onMorphisms := λ X Y f,
    show l (F' X) ⟶ l (F' Y), from
    id_of_eq (e Y) ∘ (F &> f) ∘ id_of_eq (e X).symm,
  identities := λ X, by dsimp [induced_category]; rw F.identities; simp,
  functoriality := λ X Y Z f g, by dsimp [induced_category]; rw F.functoriality; simp }

def induced_functor_gpd [gpdC : groupoid.{u v} C] [gpdD : groupoid.{w x} D] (F : C ↝ D)
  (F' : C' → D') (e : ∀ a, F.onObjects (k a) = l (F' a)) :
  @functor.Functor C' (induced_groupoid k gpdC).to_category D' (induced_groupoid l gpdD).to_category :=
induced_functor k l F F' e

lemma induced_functor_id [catC : category.{u v} C] :
  induced_functor k k (functor.IdentityFunctor C) id (λ a, rfl) =
  @functor.IdentityFunctor C' (induced_category k catC) :=
begin
  fapply functor.Functor.ext,
  { intro a, refl },
  { intros a b f, dsimp [induced_functor], simp }
end

variables {E : Type y} {E' : Type y'} (m : E' → E)
lemma induced_functor_comp [catC : category.{u v} C]
  [catD : category.{w x} D] [catE : category.{y z} E]
  {F : C ↝ D} {F' : C' → D'} (eF : ∀ a, F.onObjects (k a) = l (F' a))
  {G : D ↝ E} {G' : D' → E'} (eG : ∀ a, G.onObjects (l a) = m (G' a)) :
  induced_functor k m (functor.FunctorComposition F G) (function.comp G' F')
    (by intro a; change G +> (F +> k a) = _; rw [eF, eG]) =
  @functor.FunctorComposition
    C' (induced_category k catC)
    D' (induced_category l catD)
    E' (induced_category m catE)
    (induced_functor k l F F' eF) (induced_functor l m G G' eG) :=
begin
  fapply functor.Functor.ext,
  { intro a, refl },
  { intros a b f, dsimp [induced_functor], simp, refl }
end

end categories
