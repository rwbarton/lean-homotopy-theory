import .homotopy_classes

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder

section
/-

Suppose f₀ : b → x is a map and G is a homotopy from u = f₀ ∘ j to
some other map u' : a → x. Using the homotopy extension property of j,
we obtain a homotopy f₀ ≃ f₁ extending G to a map f₁ with f₁ ∘ j = u'.
We show below that this construction is well-defined up to homotopy
rel j and defines a bijection between homotopy classes rel j of maps
extending u and homotopy classes rel j of maps extending u'.

This correspondence is not constructive in either direction since we
need to use the HEP, which is a mere existence statement. Therefore we
describe it as a relation and show that a homotopy class on either
side is related to a unique homotopy class on the other side.

We call this the "drag" relation induced by G, and imagine dragging
the restriction of f₀ to a along the homotopy G, with the rest of f₀
following along. A familiar example is the isomorphism πₙ(X, x) ≃
πₙ(X, y) induced by a path γ : x ↝ y in X.

-/

parameters {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

parameters {a b : C} {j : a ⟶ b} (hj : is_cof j) {x : C}
include hj

section dir
-- Abstract over the direction of "dragging": f₀ to f₁ or f₁ to f₀.
parameters (u : endpoint → (a ⟶ x))
parameters (ε : endpoint) (G : homotopy_dir ε (u ε) (u ε.v))
include G

def drag_rel_dir : maps_extending hj (u ε) → maps_extending hj (u ε.v) → Prop :=
λ fε fεv, ∃ H : homotopy_dir ε fε.val fεv.val, H.H ∘ I &> j = G.H

lemma total (fε : maps_extending hj (u ε)) : ∃ fεv, drag_rel_dir fε fεv :=
let ⟨E, h₁, h₂⟩ := I_category.hep_cof j hj ε x fε.val G.H $
  by rw [fε.property, G.Hiε] in
⟨⟨E ∘ i ε.v @> b, by rw [i_nat_assoc, ←G.Hiεv, h₂]⟩,
 ⟨homotopy_dir.mk ε E h₁ rfl, by clear _let_match; cases ε; exact h₂⟩⟩

end dir

parameters (u u' : a ⟶ x)
parameters (G : homotopy u u')
include G

def drag_rel : maps_extending hj u → maps_extending hj u' → Prop :=
λ f₀ f₁, ∃ H : homotopy f₀.val f₁.val, H.H ∘ I &> j = G.H

local notation f₀ ` ~G `:50 f₁:50 := drag_rel f₀ f₁
local notation `[` b `,` x `]^` u:60 := homotopy_classes_extending_rel j hj u

-- The relation ~G does not descend to the quotient: given a homotopy
-- f₀ ≃ f₀' rel u and a homotopy f₀ ≃ f₁ extending G, we may not be
-- able to find a homotopy f₀' ≃ f₁ extending G. Rather, two homotopy
-- classes are related when they have representatives which are
-- related by ~G.
def drag_rel_homotopy : [b, x]^u → [b, x]^u' → Prop :=
λ g₀ g₁, ∃ f₀ f₁, ⟦f₀⟧ = g₀ ∧ ⟦f₁⟧ = g₁ ∧ f₀ ~G f₁

private def uu' : endpoint → (a ⟶ x) := λ ε, endpoint.cases_on ε u u'

lemma drag_rel_homotopy_total₀ (g₀) : ∃ g₁, drag_rel_homotopy g₀ g₁ :=
quotient.induction_on g₀ $ assume f₀,
  let ⟨f₁, h⟩ := total uu' 0 G f₀ in ⟨⟦f₁⟧, ⟨f₀, f₁, rfl, rfl, h⟩⟩

lemma drag_rel_homotopy_total₁ (g₁) : ∃ g₀, drag_rel_homotopy g₀ g₁ :=
quotient.induction_on g₁ $ assume f₁,
  let ⟨f₀, h⟩ := total uu' 1 G f₁ in ⟨⟦f₀⟧, ⟨f₀, f₁, rfl, rfl, h⟩⟩

lemma drag_rel_homotopy_unique₀ (g₀ g₁ g₁') :
  drag_rel_homotopy g₀ g₁ → drag_rel_homotopy g₀ g₁' → g₁ = g₁' :=
assume ⟨f₀, f₁, hf₀, hf₁, ⟨H, h⟩⟩ ⟨f₀', f₁', hf₀', hf₁', ⟨H', h'⟩⟩,
  have f₀.val ≃ f₀'.val rel j, from quotient.exact (hf₀.trans hf₀'.symm),
  let ⟨H₀, h₀⟩ := this in
  hf₁.symm.trans $
    (quotient.sound (equiv_private.f₁_f₂ j hj h₀ 0 h h') : ⟦f₁⟧ = ⟦f₁'⟧).trans hf₁'

lemma drag_rel_homotopy_unique₁ (g₀ g₀' g₁) :
  drag_rel_homotopy g₀ g₁ → drag_rel_homotopy g₀' g₁ → g₀ = g₀' :=
assume ⟨f₀, f₁, hf₀, hf₁, ⟨H, h⟩⟩ ⟨f₀', f₁', hf₀', hf₁', ⟨H', h'⟩⟩,
  have f₁.val ≃ f₁'.val rel j, from quotient.exact (hf₁.trans hf₁'.symm),
  let ⟨H₁, h₁⟩ := this in
  hf₀.symm.trans $
    (quotient.sound (equiv_private.f₁_f₂ j hj h₁ 1 h h') : ⟦f₀⟧ = ⟦f₀'⟧).trans hf₀'

end
end homotopy_theory.cofibrations
