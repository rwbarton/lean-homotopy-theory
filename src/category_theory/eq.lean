import category_theory.base
import category_theory.functor

/-

Non-definitional equalities between objects of a category can be
awkward to work with. For example, suppose we want to show that two
functors F, G : C → D are equal. First we need to show that FA = GA
for every object A of C. Then, for every morphism f : A → B in C, we
need to show that Ff = Gf; but the two sides of this equality do not
have definitionally equal types. We must either use recursion on the
equalities FA = GA and FB = GB, or use heterogeneous equality; either
way, proofs become more difficult.

The algebraic structure of categories provides a more convenient way
to keep track of equalities between objects. Namely, for each equality
e : X = X', there is an associated "equator" morphism X → X', which is
just the identity morphism of X (or of X'). We call this morphism
`id_to_eq e`. By composing with these morphisms, we can change the
domain or codomain of a morphism to a propositionally equal object,
allowing us to compare morphisms with non-definitionally equal types,
like Ff and Gf in the example above. The "equator" morphisms satisfy
simple algebraic identities, making proofs about them easy.

-/

universes v x u w

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace category_theory

variables {C : Type u} [catC : category.{v} C]
include catC

variables {D : Type w} [catD : category.{x} D]
include catD

-- Proving equality between functors.
lemma functor.hext {F G : C ↝ D}
  (h_ob : ∀ a, F.obj a = G.obj a)
  (h_mor : ∀ {a b : C} (f : a ⟶ b), F &> f == G &> f) : F = G :=
begin
  cases F, cases G,
  have : F_obj = G_obj := funext h_ob, subst this,
  congr,
  funext a b f,
  have := h_mor f, simp at this, exact this
end

end category_theory
