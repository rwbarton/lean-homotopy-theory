import .colimit_lemmas

open category_theory.category set
local notation f ` ∘ `:80 g:80 := g ≫ f

/-
   a ⊔ a  →    a
     ↓         ↓
  b₀ ⊔ b₁ → b₀ ⊔ b₁
               a
-/

universes v u

namespace category_theory

section

parameters {C : Type u} [category.{v} C] [has_coproducts.{v} C]

def with_precomposition_bij {a' a x : C} (f : a' ⟶ a) :
  Bij_on (λ (k : a ⟶ x), (k, k ∘ f)) univ {p | p.2 = p.1 ∘ f} :=
Bij_on.mk_univ
  { to_fun := λ k, ⟨(k, k ∘ f), rfl⟩,
    inv_fun := λ p, p.val.1,
    left_inv := λ k, by simp,
    right_inv := λ p, by rcases p with ⟨⟨k, kf⟩, h⟩; dsimp; congr; exact h.symm }
  (λ k, rfl)

parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁}
parameters {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c} (po : Is_pushout f₀ f₁ g₀ g₁)

local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

def Is_pushout_fold :
  Is_pushout (coprod_of_maps f₀ f₁) (coprod.fold a) (coprod.induced g₀ g₁) (g₀ ∘ f₀) :=
Is_pushout.mk $ λ x,
  have _ := calc
  univ ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | p.1 ∘ f₀ = p.2 ∘ f₁} : po.universal x
  ...  ~~ {p : (b₀ ⟶ x) × (b₁ ⟶ x) | _}
       : Bij_on.congr_subset (by ext p; simp)
  ...  ~~ {q : b₀ ⊔ b₁ ⟶ x | (q ∘ i₀) ∘ f₀ = (q ∘ i₁) ∘ f₁}
       : Bij_on.restrict'' (Bij_on.of_Is_equiv coprod.induced_Is_equiv) _
  ...  ~~ {q : b₀ ⊔ b₁ ⟶ x | _} : Bij_on.congr_subset (by ext q; simp; refl)
  ...  ~~ {p : (b₀ ⊔ b₁ ⟶ x) × (a ⟶ x)
          | (p.1 ∘ i₀) ∘ f₀ = (p.1 ∘ i₁) ∘ f₁ ∧ p.2 = p.1 ∘ (i₀ ∘ f₀)}
       : Bij_on.restrict' (with_precomposition_bij (i₀ ∘ f₀)) _
  ...  ~~ {p : (b₀ ⊔ b₁ ⟶ x) × (a ⟶ x) | p.1 ∘ coprod_of_maps f₀ f₁ = p.2 ∘ coprod.fold a}
       : Bij_on.congr_subset begin
           ext p, dsimp,
           conv
           { to_rhs,
             rw [coprod.ext, ←assoc, ←assoc, ←assoc, ←assoc],
             rw [coprod_of_maps_commutes₀, coprod_of_maps_commutes₁],
             rw [coprod.fold_i₀, coprod.fold_i₁],
             rw [assoc, assoc, id_comp] },
           rw assoc,
           split; rintros ⟨h₁, h₂⟩; refine ⟨_, _⟩; cc
         end,
  begin
    convert this,
    ext k,
    { dsimp, rw ←category.assoc, simp },
    { dsimp, rw ←category.assoc, simp },
    { simp }
  end

end
end category_theory
