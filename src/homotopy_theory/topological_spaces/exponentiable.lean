import topology.compact_open
import category_theory.adjunction
import for_mathlib

import .category

universe u

open continuous_map
open category_theory category_theory.adjunction
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{u}

/-

A space A is exponentiable if the functor - × A admits a right adjoint
functor [A, -]. This means that for all spaces X and Y, there is a
natural isomorphism of sets

  C(Y × A, X) ≃ C(Y, [A, X]),

where C denotes the set of continuous maps. By taking Y = * so that
C(Y, -) is the underlying set functor, one sees that the only possible
choice for the underlying set of [A, X] is the set C(A, X). We
therefore define a space A to be exponentiable if C(A, X) can be
equipped with a topology for each X which is (1) functorial with
respect to continuous maps X → X' and (2) such that the evaluation and
coevaluation maps (which form the counit and unit of the
product-exponential adjunction on Set) are continuous.

-/

variables (A X : Top)

def ev : (A ⟶ X) × A → X := λ p, p.1 p.2

def coev : X → (A ⟶ Top.prod X A) :=
λ b, Top.mk_hom (λ a, (b, a)) (by continuity)

variables {X} {X' : Top}
def induced : (X ⟶ X') → (A ⟶ X) → (A ⟶ X') :=
λ f g, f ∘ g

class exponentiable (A : Top) :=
(exponential     : Π (X : Top), topological_space (A ⟶ X))
(functorial      : ∀ (X X' : Top) (g : X ⟶ X'), continuous (induced A g))
(continuous_ev   : ∀ (X : Top), continuous (ev A X))
(continuous_coev : ∀ (X : Top), continuous (coev A X))

instance exponentiable.topological_space (A X : Top) [exponentiable A] :
  topological_space (A ⟶ X) :=
exponentiable.exponential A X

-- Now we can define the exponential functor [A, -] and show that it
-- is right adjoint to - × A.
def exponential (A : Top) [exponentiable A] (X : Top) : Top :=
Top.mk_ob (A ⟶ X)

def exponential_induced (A : Top) [exponentiable A] (X X' : Top) (g : X ⟶ X')
  : exponential A X ⟶ exponential A X' :=
Top.mk_hom (induced A g) (exponentiable.functorial A X X' g)

def exponential_functor (A : Top) [exponentiable A] : Top ↝ Top :=
{ obj := exponential A,
  map := exponential_induced A,
  map_id' := by intro X; ext g x; refl,
  map_comp' := by intros X X' X'' f g; refl }

def exponential_adjunction (A : Top) [exponentiable A] : (-× A) ⊣ exponential_functor A :=
adjunction.mk_of_unit_counit $
{ unit :=
    { app := λ X, Top.mk_hom (coev A X) (exponentiable.continuous_coev A X) },
  counit :=
    { app := λ X, Top.mk_hom (ev A X) (exponentiable.continuous_ev A X) },
  left_triangle' := by ext X xa; cases xa; refl,
  right_triangle' := by ext X f a; refl }

local attribute [class] is_left_adjoint

instance (A : Top) [exponentiable A] : is_left_adjoint (-× A) :=
{ right := exponential_functor A,
  adj := exponential_adjunction A }

-- Locally compact spaces are exponentiable by equipping A ⟶ X with
-- the compact-open topology.
instance (A : Top) [locally_compact_space A] : exponentiable A :=
{ exponential := λ _, continuous_map.compact_open,
  functorial := assume X X' g, continuous_induced g.property,
  continuous_ev := assume X, continuous_ev,
  continuous_coev := assume X, continuous_coev }

end homotopy_theory.topological_spaces
