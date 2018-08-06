import categories.category
import categories.functor

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

universes u v w x

local notation f ` ∘ `:80 g:80 := g ≫ f

namespace categories

variables {C : Type u} [catC : category.{u v} C]
include catC

def id_of_eq {a b : C} (e : a = b) : a ⟶ b := e.rec_on (𝟙 a)

@[simp] lemma id_of_eq.refl {a : C} (e : a = a) : id_of_eq e = 𝟙 a :=
rfl

@[simp] lemma id_of_eq.trans {a b c : C} (e : a = b) (e' : b = c) :
  id_of_eq e' ∘ id_of_eq e = id_of_eq (e.trans e') :=
by cases e; cases e'; simp

@[simp] lemma id_of_eq.trans_assoc {a b c z : C} (e : a = b) (e' : b = c) (g : c ⟶ z) :
  g ∘ id_of_eq e' ∘ id_of_eq e = g ∘ id_of_eq (e.trans e') :=
by cases e; cases e'; simp

variables {D : Type w} [catD : category.{w x} D]
include catD

@[simp] lemma id_of_eq.map {a b : C} (F : C ↝ D) (e : a = b) :
  F &> id_of_eq e = id_of_eq (congr_arg F.onObjects e) :=
by cases e; simp

-- Proving equality between functors.
-- TODO: Deduplicate
infixr ` &> `:85 := functor.Functor.onMorphisms

lemma functor.Functor.ext {F G : C ↝ D}
  (h_ob : ∀ a, F +> a = G +> a)
  (h_mor : ∀ {a b : C} (f : a ⟶ b),
    id_of_eq (h_ob b) ∘ F &> f = G &> f ∘ id_of_eq (h_ob a)) : F = G :=
begin
  cases F, cases G,
  have : F_onObjects = G_onObjects := funext h_ob, subst this,
  congr,
  funext a b f,
  have := h_mor f, simp at this, exact this
end

lemma functor.Functor.hext {F G : C ↝ D}
  (h_ob : ∀ a, F +> a = G +> a)
  (h_mor : ∀ {a b : C} (f : a ⟶ b), F &> f == G &> f) : F = G :=
begin
  cases F, cases G,
  have : F_onObjects = G_onObjects := funext h_ob, subst this,
  congr,
  funext a b f,
  have := h_mor f, simp at this, exact this
end

end categories
