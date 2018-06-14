import categories.functor_categories

namespace categories
open category

local notation f ` ∘ `:80 g:80 := g ≫ f
local notation F ` ∘ᶠ `:80 G:80 := functor.FunctorComposition G F
local infixr ` &> `:85 := functor.Functor.onMorphisms
local notation t ` @> `:90 X:90 := t.components X

universes u₁ v₁ u₂ v₂
variables {C : Type u₁} [catC : category.{u₁ v₁} C]
variables {D : Type u₂} [catD : category.{u₂ v₂} D]
include catC catD

-- This split apparently helps the elaborator understand that `unit`
-- and `counit` are natural transformations in the triangle laws.
structure adjunction_data (F : C ↝ D) (G : D ↝ C) :=
(unit : 1 ⟶ G ∘ᶠ F)
(counit : F ∘ᶠ G ⟶ 1)

local attribute [elab_simple] functor.Functor.onMorphisms
-- TODO: Think about binding powers of these operators?
-- Actually, seems more or less okay
structure adjunction (F : C ↝ D) (G : D ↝ C) extends adjunction_data F G :=
(left_triangle : ∀ (c : C), counit @> (F +> c) ∘ F &> unit @> c = 𝟙 _)
(right_triangle : ∀ (d : D), G &> counit @> d ∘ unit @> (G +> d) = 𝟙 _)

attribute [simp] adjunction.left_triangle adjunction.right_triangle

class has_right_adjoint (F : C ↝ D) :=
(right_adjoint : D ↝ C)
(adj : adjunction F right_adjoint)

variables {F : C ↝ D} {G : D ↝ C}
def adjunction.hom_equivalence (adj : adjunction F G) (c d) :
  (F +> c ⟶ d) ≃ (c ⟶ G +> d) :=
{ to_fun := λ f, G &> f ∘ adj.unit @> c,
  inv_fun := λ g, adj.counit @> d ∘ F &> g,
  left_inv := λ f, begin
    change _ ∘ F &> (_ ∘ _) = _,
    rw [F.functoriality, associativity], change _ ∘ (F ∘ᶠ G) &> f ∘ _ = _,
    rw [adj.counit.naturality, ←associativity, adj.left_triangle],
    exact category.left_identity D f
  end,
  right_inv := λ g, begin
    change G &> (_ ∘ _) ∘ _ = _,
    rw [G.functoriality, ←associativity], change _ ∘ ((G ∘ᶠ F) &> g ∘ _) = _,
    rw [←adj.unit.naturality, associativity, adj.right_triangle],
    exact category.right_identity C g
  end }

lemma adjunction.hom_equivalence_symm_naturality (adj : adjunction F G) {c' c d}
  (f : c' ⟶ c) (g : c ⟶ G +> d) :
  (adj.hom_equivalence c' d).symm (g ∘ f) =
  (adj.hom_equivalence c d).symm g ∘ F &> f :=
show adj.counit @> d ∘ F &> (g ∘ f) = adj.counit @> d ∘ F &> g ∘ F &> f,
by simp

end categories
