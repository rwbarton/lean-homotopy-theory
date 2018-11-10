import category_theory.base
import category_theory.natural_transformation
import category_theory.functor_category
import category_theory.colimit_lemmas

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f
local notation F ` ∘ᶠ `:80 G:80 := G.comp F

universes u v

-- TODO: Move these elsewhere
notation t ` @> `:90 X:90 := t.app X

namespace homotopy_theory.cylinder

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
(i : endpoint → (functor.id C ⟶ I))
(p : I ⟶ functor.id C)
(pi : ∀ ε, p ∘ i ε = nat_trans.id _)

section
parameters {C : Type u} [cat : category C] [has_cylinder C]
include cat

def I : C ↝ C :=
has_cylinder.I C

@[reducible] def i : Π ε, functor.id C ⟶ I :=
has_cylinder.i C

@[reducible] def p : I ⟶ functor.id C :=
has_cylinder.p C

@[simp] lemma pi_components (ε) {A : C} : p.app A ∘ (i ε).app A = 𝟙 A :=
show (p ∘ (i ε)).app A = 𝟙 A,
by erw has_cylinder.pi; refl

lemma i_nat_assoc (ε) {y z w : C} (g : I.obj z ⟶ w) (h : y ⟶ z) :
  g ∘ i ε @> z ∘ h = g ∘ I &> h ∘ i ε @> y :=
by erw [←assoc, (i ε).naturality]; simp

lemma p_nat_assoc {y z w : C} (g : z ⟶ w) (h : y ⟶ z) :
  g ∘ p @> z ∘ I &> h = g ∘ h ∘ p @> y :=
by erw [←assoc, p.naturality]; simp

end


section boundary
variables {C : Type u} [cat : category.{u v} C] [has_coproducts.{u v} C]
include cat

-- If C admits coproducts, then we can combine the inclusions `i 0`
-- and `i 1` into a single natural transformation `∂I ⟶ I`, where `∂I`
-- is defined by `∂I A = A ⊔ A`. (`∂I` does not depend on `I`.)
def boundary_I : C ↝ C :=
{ obj := λ A, A ⊔ A,
  map := λ A B f, coprod_of_maps f f,
  map_id' := λ A, by apply coprod.uniqueness; simp,
  map_comp' := λ A B C f g, by apply coprod.uniqueness; rw ←assoc; simp }

notation `∂I` := boundary_I

variables [has_cylinder C]

def ii : ∂I ⟶ I :=
show ∂I ⟶ (I : C ↝ C), from
{ app := λ (A : C), coprod.induced (i 0 @> A) (i 1 @> A),
  naturality' := λ A B f,
  begin
    dsimp [boundary_I],
    apply coprod.uniqueness;
      { rw [←assoc, ←assoc], simpa using (i _).naturality f }
  end }

@[simp] lemma iii₀_assoc {A B : C} (f : I.obj A ⟶ B) : f ∘ ii.app A ∘ i₀ = f ∘ (i 0).app A :=
by rw ←assoc; dsimp [ii]; simp

@[simp] lemma iii₁_assoc {A B : C} (f : I.obj A ⟶ B) : f ∘ ii.app A ∘ i₁ = f ∘ (i 1).app A :=
by rw ←assoc; dsimp [ii]; simp

end boundary


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
(vv : v ∘ v = 𝟙 _)
(pv : p ∘ v = p)

section
parameters {C : Type u} [cat : category C] [has_cylinder_with_involution C]
include cat

@[reducible] def v : I ⟶ I :=
has_cylinder_with_involution.v C

@[simp] lemma vi_components {A : C} (ε) : v @> A ∘ i ε @> A = i ε.v @> A :=
show (v ∘ i ε) @> A = (i ε.v) @> A,
by rw has_cylinder_with_involution.vi; refl

@[simp] lemma vv_components {A : C} : v @> A ∘ v @> A = 𝟙 (I.obj A) :=
show (v ∘ v) @> A = _,
by rw has_cylinder_with_involution.vv; refl

end

section interchange
variables (C : Type u) [cat : category.{u v} C] [has_cylinder C]
include cat
local notation `I` := (I : C ↝ C)

-- Interchange of two applications of the cylinder functor. The
-- standard example is (on Top as above) T (x, t, t') = (x, t', t).
class cylinder_has_interchange :=
(T : I ∘ᶠ I ⟶ I ∘ᶠ I)
(Ti : ∀ ε A, T @> _ ∘ i ε @> I.obj A = I &> (i ε @> A))
(TIi : ∀ ε A, T @> _ ∘ I &> (i ε @> A) = i ε @> I.obj A)

variables [cylinder_has_interchange.{u v} C]
variables {C}

@[reducible] def T : I ∘ᶠ I ⟶ I ∘ᶠ I :=
cylinder_has_interchange.T C

end interchange

end homotopy_theory.cylinder
