import categories.natural_transformation
import categories.functor_categories

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

-- TODO: Move these elsewhere
infixr ` &> `:85 := functor.Functor.onMorphisms
notation t ` @> `:90 X:90 := t.components X

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

@[reducible] def i {C : Type u} [category C] [has_cylinder C] : Π ε, 1 ⟶ I :=
has_cylinder.i C

@[reducible] def p {C : Type u} [category C] [has_cylinder C] : I ⟶ 1 :=
has_cylinder.p C


def endpoint.v : endpoint → endpoint
| endpoint.zero := endpoint.one
| endpoint.one := endpoint.zero

@[simp] lemma endpoint.vv (ε : endpoint) : ε.v.v = ε := by cases ε; refl

-- "Time-reversal" on a cylinder functor. The standard example is (on
-- Top as above) v (x, t) = (x, 1 - t).
--
-- The condition v² = 1 is not in Williamson; we add it here because
-- it holds in the standard examples and lets us reverse the homotopy
-- extension property. (Actually it would be enough for v to be an
-- isomorphism.)
class has_cylinder_with_involution (C : Type u) [category C]
  extends has_cylinder C :=
(v : I ⟶ I)
(vi : ∀ ε, v ∘ i ε = i ε.v)
(vv : v ∘ v = 1)
(pv : p ∘ v = p)

section
parameters {C : Type u} [cat : category C] [has_cylinder_with_involution C]
include cat

@[reducible] def v : I ⟶ I :=
has_cylinder_with_involution.v C

@[simp] lemma vi_components {A : C} (ε) : v @> A ∘ i ε @> A = i ε.v @> A :=
show (v ∘ i ε) @> A = (i ε.v) @> A,
by rw has_cylinder_with_involution.vi; refl

@[simp] lemma vv_components {A : C} : v @> A ∘ v @> A = 𝟙 _ :=
show (v ∘ v) @> A = (1 : I ⟹ I) @> A,
by rw has_cylinder_with_involution.vv; refl

end

end homotopy_theory.cylinder
