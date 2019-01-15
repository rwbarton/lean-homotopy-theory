import .precofibration_category

universes v u

namespace homotopy_theory.cofibrations
open category_theory category_theory.category
open precofibration_category

variables {C : Type u} [𝒞 : category.{v} C] [precofibration_category.{v} C]
include 𝒞

-- These are the cofibrations in the arrow category of C with the "projective" structure.
structure cof_square {a₁ a₂ b₁ b₂ : C} (a : a₁ ⟶ a₂) (b : b₁ ⟶ b₂) : Type (max u v) :=
(f₁ : a₁ ⟶ b₁)
(f₂ : a₂ ⟶ b₂)
(hs : f₁ ≫ b = a ≫ f₂)
(hf₁ : is_cof f₁)
(hf₂ : is_cof ((pushout_by_cof f₁ a hf₁).is_pushout.induced b f₂ hs))

def cof_square.id {a₁ a₂ : C} (a : a₁ ⟶ a₂) : cof_square a a :=
⟨𝟙 a₁, 𝟙 a₂, by simp, cof_id _,
/-
  a₁ = a₁
  ↓    ↓
  a₂ = a₂
-/
 begin
   let := pushout.unique (pushout_by_cof (𝟙 a₁) a (cof_id _)).is_pushout
     (Is_pushout.refl a).transpose,
   exact cof_iso this
 end⟩

def cof_square.comp {a₁ a₂ b₁ b₂ c₁ c₂ : C} {a : a₁ ⟶ a₂} {b : b₁ ⟶ b₂} {c : c₁ ⟶ c₂}
  (f : cof_square a b) (g : cof_square b c) : cof_square a c :=
⟨f.f₁ ≫ g.f₁,
 f.f₂ ≫ g.f₂,
 by rw [assoc, g.hs, ←assoc, f.hs, assoc],
 cof_comp f.hf₁ g.hf₁,
 begin
/-
  a₁ → b₁ → c₁   All these pushouts are "transposed" from the usual layout,
  ↓  1 ↓  2 ↓    that is, the first map is horizontal and the second vertical.
  a₂ → ⬝  → ⬝
       ↓  3 ↓
       b₂ → ⬝
            ↓
            c₂
-/
   let po₁ := pushout_by_cof f.f₁ a f.hf₁,
   let po₁₂ := pushout_by_cof (f.f₁ ≫ g.f₁) a (cof_comp f.hf₁ g.hf₁),
   let k :=
     pushout_of_maps po₁.is_pushout po₁₂.is_pushout (𝟙 a₁) g.f₁ (𝟙 a₂) (by simp) (by simp),
   have po₂ : Is_pushout g.f₁ po₁.map₀ po₁₂.map₀ k :=
     Is_pushout_of_Is_pushout_of_Is_pushout_vert' po₁.is_pushout
       (by convert po₁₂.is_pushout; simp [k, pushout_of_maps])
       (by simp [k, pushout_of_maps]),
   let fc := _,
   have : is_cof fc := f.hf₂,
   let po₂₃ := pushout_by_cof g.f₁ b g.hf₁,
   let l :=
     pushout_of_maps po₁₂.is_pushout po₂₃.is_pushout f.f₁ (𝟙 c₁) f.f₂ (by simp) f.hs.symm,
   have po₃ : Is_pushout k fc l po₂₃.map₁ :=
     Is_pushout_of_Is_pushout_of_Is_pushout' po₂
       (by convert po₂₃.is_pushout; simp [l, pushout_of_maps])
       begin
         apply po₁.is_pushout.uniqueness;
         dsimp [k, fc, pushout_of_maps];
         conv { to_lhs, rw ←assoc };
         conv { to_rhs, rw ←assoc };
         simp [l, pushout_of_maps, po₂₃.is_pushout.commutes]
       end,
   let gc := _,
   have : is_cof gc := g.hf₂,
   convert cof_comp (pushout_is_cof po₃.transpose f.hf₂) g.hf₂,
   simp [l, induced_pushout_of_maps]
 end⟩

section is_cof_square

/- This "flatter" representation is helpful when trying to prove that a square's
  corner map is a cofibration by expressing it as (non-definitionally equal to)
  a composition of two such squares. -/

variables {a₁ a₂ b₁ b₂ c₁ c₂ : C} (a : a₁ ⟶ a₂) (b : b₁ ⟶ b₂) {c : c₁ ⟶ c₂}
variables (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) {g₁ : b₁ ⟶ c₁} {g₂ : b₂ ⟶ c₂}
variables {h₁ : a₁ ⟶ c₁} {h₂ : a₂ ⟶ c₂}

def is_cof_square : Prop :=
∃ s : cof_square a b, s.f₁ = f₁ ∧ s.f₂ = f₂

variables {a b f₁ f₂}

lemma is_cof_square.corner_cof (H : is_cof_square a b f₁ f₂) :
  ∃ (hf₁ : is_cof f₁) (hs : f₁ ≫ b = a ≫ f₂),
  is_cof ((pushout_by_cof f₁ a hf₁).is_pushout.induced b f₂ hs) :=
begin
  rcases H with ⟨c, hc₁, hc₂⟩,
  subst f₁,
  subst f₂,
  exact ⟨c.hf₁, c.hs, c.hf₂⟩
end

lemma is_cof_square_comp (Hf : is_cof_square a b f₁ f₂) (Hg : is_cof_square b c g₁ g₂)
  (Hh₁ : h₁ = f₁ ≫ g₁) (Hh₂ : h₂ = f₂ ≫ g₂) : is_cof_square a c h₁ h₂ :=
begin
  rcases Hf with ⟨cf, hcf₁, hcf₂⟩,
  rcases Hg with ⟨cg, hcg₁, hcg₂⟩,
  subst f₁, subst f₂, subst g₁, subst g₂, subst h₁, subst h₂,
  exact ⟨cf.comp cg, rfl, rfl⟩
end

end is_cof_square

end homotopy_theory.cofibrations
