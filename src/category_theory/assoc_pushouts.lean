import .pasting_pushouts

open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

/-

       a₁ → b₂         a₁ → b₂
       ↓               ↓    ↓
  a₀ → b₁   ↓     a₀ → b₁ → c₁
  ↓    ↓          ↓         ↓
  b₀ → c₀ → d     b₀   →    d'

-/

universes v u

namespace category_theory

section

parameters {C : Type u} [cat : category.{v} C]
include cat

parameters {a₀ a₁ b₀ b₁ b₂ c₀ c₁ d d' : C}
parameters {f₀ : a₀ ⟶ b₀} {f₁ : a₀ ⟶ b₁} {f₂ : a₁ ⟶ b₁} {f₃ : a₁ ⟶ b₂}
parameters {g₀ : b₀ ⟶ c₀} {g₁ : b₁ ⟶ c₀} {g₂ : b₁ ⟶ c₁} {g₃ : b₂ ⟶ c₁}
parameters {h₀ : c₀ ⟶ d} {h₁ : b₂ ⟶ d} {h₀' : b₀ ⟶ d'} {h₁' : c₁ ⟶ d'}
parameters
  (po₀ : Is_pushout f₀ f₁ g₀ g₁)
  (po₁ : Is_pushout (g₁ ∘ f₂) f₃ h₀ h₁)
  (po₂ : Is_pushout f₂ f₃ g₂ g₃)
  (po₃ : Is_pushout f₀ (g₂ ∘ f₁) h₀' h₁')
include po₀ po₁ po₂ po₃

def Is_pushout_assoc : d ≅ d' :=
begin
  refine {
    hom := po₁.induced (po₀.induced h₀' (h₁' ∘ g₂) _) (h₁' ∘ g₃) _,
    inv := po₃.induced (h₀ ∘ g₀) (po₂.induced (h₀ ∘ g₁) h₁ _) _,
    hom_inv_id' := _,
    inv_hom_id' := _,
  },
  { rw po₃.commutes, simp },
  -- TODO: Is_pushout.commutes_assoc
  { simp, rw [←assoc, ←assoc], rw po₂.commutes },
  { rw [←assoc, po₁.commutes] },
  { simp, rw [←assoc, ←assoc], rw po₀.commutes },
  { apply po₁.uniqueness; rw ←assoc; simp,
    { apply po₀.uniqueness; rw ←assoc; simp } },
  { apply po₃.uniqueness; rw ←assoc; simp,
    { apply po₂.uniqueness; rw ←assoc; simp } }
end

@[simp] lemma Is_pushout_assoc_i₀ : Is_pushout_assoc.hom ∘ h₀ ∘ g₀ = h₀' :=
by change Is_pushout.induced _ _ _ _ ∘ _ ∘ _ = _; simp

@[simp] lemma Is_pushout_assoc_i₁ : Is_pushout_assoc.hom ∘ h₁ = h₁' ∘ g₃ :=
by change Is_pushout.induced _ _ _ _ ∘ _ = _ ∘ _; simp

parameters {x : C} {k : d ⟶ x} {k' : d' ⟶ x}

lemma Is_pushout_assoc_uniqueness
  (hk₀ : k ∘ h₀ ∘ g₀ = k' ∘ h₀')
  (hk₁ : k ∘ h₀ ∘ g₁ = k' ∘ h₁' ∘ g₂)
  (hk₂ : k ∘ h₁ = k' ∘ h₁' ∘ g₃) :
  k = k' ∘ Is_pushout_assoc.hom :=
begin
  change k = k' ∘ Is_pushout.induced _ _ _ _,
  apply po₁.uniqueness; rw ←assoc,
  { apply po₀.uniqueness; conv { to_rhs, rw ←assoc },
    { rw hk₀, simp },
    { rw hk₁, simp } },
  { rw hk₂, simp }
end

end

end category_theory
