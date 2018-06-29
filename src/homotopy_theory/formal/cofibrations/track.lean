import .homotopy

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open precofibration_category -- cofibration_category

variables {C : Type u} [cat : category.{u v} C] [cofibration_category.{u v} C]
include cat

-- Tracks, or "homotopies up to homotopy". This notion is a bit tricky
-- because there is no canonical choice of cylinder object on which to
-- define homotopies. Instead, we define an equivalence relation
-- between homotopies defined on different cylinder objects and define
-- a track to be an equivalence class, and then show that every
-- cylinder object admits a unique homotopy class of homotopies
-- representing each track.

variables {a b : C} {j : a ⟶ b} (hj : is_cof j)
variables {x : C}
variables (f₀ f₁ : b ⟶ x)

structure homotopy :=
(c : relative_cylinder hj)
(h : homotopy_on c f₀ f₁)

variables {hj f₀ f₁}
-- An extension of homotopies. These are like acyclic cofibrations in
-- a category of objects under b ⊔ₐ b and over b and x, where the
-- compositions b ⊔ₐ b → b and b ⊔ₐ b → x are given by the fold map
-- and (f₀, f₁) respectively.
structure homotopy_extension (t t' : homotopy hj f₀ f₁) :=
(m : cylinder_embedding t.c t'.c)
(e : t'.h.H ∘ m.k = t.h.H)

def homotopy_extension.refl (t : homotopy hj f₀ f₁) : homotopy_extension t t :=
⟨cylinder_embedding.refl t.c, show _ ∘ 𝟙 _ = _, by simp⟩

def homotopy_extension.trans {t₀ t₁ t₂ : homotopy hj f₀ f₁}
  (m₀ : homotopy_extension t₀ t₁) (m₁ : homotopy_extension t₁ t₂) :
  homotopy_extension t₀ t₂ :=
⟨m₀.m.trans m₁.m,
 by dsimp [cylinder_embedding.trans]; rw [associativity, m₁.e, m₀.e]⟩

def homotopy_extension.pushout {t t₀ t₁ : homotopy hj f₀ f₁}
  (m₀ : homotopy_extension t t₀) (m₁ : homotopy_extension t t₁) :
  homotopy hj f₀ f₁ :=
⟨cylinder_embedding.pushout m₀.m m₁.m,
 ⟨(cylinder_embedding.pushout.is_pushout m₀.m m₁.m).induced t₀.h.H t₁.h.H
    (by rw [m₀.e, m₁.e]),
  begin
    convert t₁.h.Hi₀ using 1, unfold relative_cylinder.i₀,
    dsimp [cylinder_embedding.pushout], simp
  end,
  begin
    convert t₁.h.Hi₁ using 1, unfold relative_cylinder.i₁,
    dsimp [cylinder_embedding.pushout], simp
  end⟩⟩

def homotopy_extension.pushout.map₀ {t t₀ t₁ : homotopy hj f₀ f₁}
  (m₀ : homotopy_extension t t₀) (m₁ : homotopy_extension t t₁) :
  homotopy_extension t₀ (homotopy_extension.pushout m₀ m₁) :=
⟨cylinder_embedding.pushout.map₀ m₀.m m₁.m,
 by dsimp [cylinder_embedding.pushout.map₀, homotopy_extension.pushout]; simp⟩

def homotopy_extension.pushout.map₁ {t t₀ t₁ : homotopy hj f₀ f₁}
  (m₀ : homotopy_extension t t₀) (m₁ : homotopy_extension t t₁) :
  homotopy_extension t₁ (homotopy_extension.pushout m₀ m₁) :=
⟨cylinder_embedding.pushout.map₁ m₀.m m₁.m,
 by dsimp [cylinder_embedding.pushout.map₁, homotopy_extension.pushout]; simp⟩

-- Two homotopies are equivalent if they have a common extension.
def homotopy_equiv (t₀ t₁ : homotopy hj f₀ f₁) : Prop :=
∃ t' (m₀ : homotopy_extension t₀ t') (m₁ : homotopy_extension t₁ t'), true

-- Homotopy equivalence is an equivalence relation.
lemma homotopy_equiv.refl (t : homotopy hj f₀ f₁) : homotopy_equiv t t :=
⟨t, homotopy_extension.refl t, homotopy_extension.refl t, ⟨⟩⟩

lemma homotopy_equiv.symm {t₀ t₁ : homotopy hj f₀ f₁} :
  homotopy_equiv t₀ t₁ → homotopy_equiv t₁ t₀ :=
assume ⟨t', m₀, m₁, ⟨⟩⟩, ⟨t', m₁, m₀, ⟨⟩⟩

lemma homotopy_equiv.trans {t₀ t₁ t₂ : homotopy hj f₀ f₁} :
  homotopy_equiv t₀ t₁ → homotopy_equiv t₁ t₂ → homotopy_equiv t₀ t₂ :=
assume ⟨t, m₀, m₁, ⟨⟩⟩ ⟨t', m₁', m₂', ⟨⟩⟩,
⟨m₁.pushout m₁',
 m₀.trans (homotopy_extension.pushout.map₀ m₁ m₁'),
 m₂'.trans (homotopy_extension.pushout.map₁ m₁ m₁'),
 ⟨⟩⟩

instance homotopy_equiv.setoid : setoid (homotopy hj f₀ f₁) :=
{ r := homotopy_equiv,
  iseqv :=
    ⟨λ t, homotopy_equiv.refl t,
     λ t₀ t₁, homotopy_equiv.symm,
     λ t₀ t₁ t₂, homotopy_equiv.trans⟩ }

variables (hj f₀ f₁)
def track := quotient (homotopy_equiv.setoid : setoid (homotopy hj f₀ f₁))

end homotopy_theory.cofibrations
