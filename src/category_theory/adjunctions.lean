import category_theory.base
import category_theory.functor_category
import data.equiv.basic

namespace category_theory
open category

local notation f ` ∘ `:80 g:80 := g ≫ f
local notation F ` ∘ᶠ `:80 G:80 := G.comp F

universes v₁ v₂ u₁ u₂
variables {C : Type u₁} [catC : category.{v₁} C]
variables {D : Type u₂} [catD : category.{v₂} D]
include catC catD

-- This split apparently helps the elaborator understand that `unit`
-- and `counit` are natural transformations in the triangle laws.
structure adjunction_data (F : C ↝ D) (G : D ↝ C) :=
(unit : functor.id _ ⟶ G ∘ᶠ F)
(counit : F ∘ᶠ G ⟶ functor.id _)

local attribute [elab_simple] functor.map
-- TODO: Think about binding powers of these operators?
-- Actually, seems more or less okay
structure adjunction (F : C ↝ D) (G : D ↝ C) extends adjunction_data F G :=
(left_triangle : ∀ (c : C), counit.app (F.obj c) ∘ F &> unit.app c = 𝟙 _)
(right_triangle : ∀ (d : D), G &> counit.app d ∘ unit.app (G.obj d) = 𝟙 _)

attribute [simp] adjunction.left_triangle adjunction.right_triangle

class has_right_adjoint (F : C ↝ D) :=
(right_adjoint : D ↝ C)
(adj : adjunction F right_adjoint)

variables {F : C ↝ D} {G : D ↝ C}
def adjunction.hom_equivalence (adj : adjunction F G) (c d) :
  (F.obj c ⟶ d) ≃ (c ⟶ G.obj d) :=
{ to_fun := λ f, G &> f ∘ adj.unit.app c,
  inv_fun := λ g, adj.counit.app d ∘ F &> g,
  left_inv := λ f, begin
    change _ ∘ F &> (_ ∘ _) = _,
    rw [F.map_comp, assoc], change _ ∘ (F ∘ᶠ G) &> f ∘ _ = _,
    erw [adj.counit.naturality, ←assoc, adj.left_triangle],
    exact category.id_comp D f
  end,
  right_inv := λ g, begin
    change G &> (_ ∘ _) ∘ _ = _,
    rw [G.map_comp, ←assoc], change _ ∘ ((G ∘ᶠ F) &> g ∘ _) = _,
    erw [←adj.unit.naturality, assoc, adj.right_triangle],
    exact category.comp_id C g
  end }

lemma adjunction.hom_equivalence_symm_naturality (adj : adjunction F G) {c' c d}
  (f : c' ⟶ c) (g : c ⟶ G.obj d) :
  (adj.hom_equivalence c' d).symm (g ∘ f) =
  (adj.hom_equivalence c d).symm g ∘ F &> f :=
show adj.counit.app d ∘ F &> (g ∘ f) = adj.counit.app d ∘ F &> g ∘ F &> f,
by simp

end category_theory
