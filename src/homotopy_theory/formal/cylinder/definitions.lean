import categories.natural_transformation
import categories.functor_categories

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cylinder

universe u


-- An "abstract endpoint" of a "cylinder"; there are two.
inductive endpoint
| zero
| one

instance : has_zero endpoint := ⟨endpoint.zero⟩
instance : has_one endpoint := ⟨endpoint.one⟩

-- A cylinder functor (with contraction). We treat the contraction as
-- part of the basic structure as it is needed to define "homotopy
-- rel".
--
-- The standard example is C = Top, IX = X × [0,1], i ε x = (x, ε),
-- p (x, t) = x.
class has_cylinder (C : Type u) [category C] :=
(I : C ↝ C)
(i : endpoint → (1 ⟶ I))
(p : I ⟶ 1)
(pi : ∀ ε, p ∘ i ε = 1)

def I {C : Type u} [category C] [has_cylinder C] : C ↝ C :=
has_cylinder.I C

def i {C : Type u} [category C] [has_cylinder C] : Π ε, 1 ⟶ I :=
has_cylinder.i C

def p {C : Type u} [category C] [has_cylinder C] : I ⟶ 1 :=
has_cylinder.p C


def endpoint.v : endpoint → endpoint
| endpoint.zero := endpoint.one
| endpoint.one := endpoint.zero

-- "Time-reversal" on a cylinder functor. The standard example is (on
-- Top as above) v (x, t) = (x, 1 - t).
class has_cylinder_with_involution (C : Type u) [category C]
  extends has_cylinder C :=
(v : I ⟶ I)
(vi : ∀ ε, v ∘ i ε = i ε.v)
(pv : p ∘ v = p)

def v {C : Type u} [category C] [has_cylinder_with_involution C] : I ⟶ I :=
has_cylinder_with_involution.v C


end homotopy_theory.cylinder
