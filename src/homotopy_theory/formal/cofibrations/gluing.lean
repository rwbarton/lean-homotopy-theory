import .brown

universes u v

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open precofibration_category cofibration_category
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{u v} C] [cofibration_category.{u v} C]
  [has_initial_object.{u v} C]
include cat

-- Following Rădulescu-Banu, Cofibrations in Homotopy Theory, Lemma 1.4.1

variables {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : C}
  {f₁₂ : a₁ ⟶ a₂} {f₁₃ : a₁ ⟶ a₃} {f₂₄ : a₂ ⟶ a₄} {f₃₄ : a₃ ⟶ a₄}
  (po_f : Is_pushout f₁₂ f₁₃ f₂₄ f₃₄)
  {g₁₂ : b₁ ⟶ b₂} {g₁₃ : b₁ ⟶ b₃} {g₂₄ : b₂ ⟶ b₄} {g₃₄ : b₃ ⟶ b₄}
  (po_g : Is_pushout g₁₂ g₁₃ g₂₄ g₃₄)
  {u₁ : a₁ ⟶ b₁} {u₂ : a₂ ⟶ b₂} {u₃ : a₃ ⟶ b₃} -- u₄ will be the induced map of pushouts
  (ha₁ : cofibrant a₁) (ha₃ : cofibrant a₃) (hb₁ : cofibrant b₁) (hb₃ : cofibrant b₃)
  (hf₁₂ : is_cof f₁₂) (hg₁₂ : is_cof g₁₂)
  (hwu₁ : is_weq u₁) (hwu₂ : is_weq u₂) (hwu₃ : is_weq u₃)
  (s₁₂ : f₁₂ ≫ u₂ = u₁ ≫ g₁₂) (s₁₃ : f₁₃ ≫ u₃ = u₁ ≫ g₁₃)

lemma gluing_weq_aux (hcu₁ : is_cof u₁) (hcu₃ : is_cof u₃)
  (hcu₂'' : is_cof ((pushout_by_cof f₁₂ u₁ hf₁₂).is_pushout.induced u₂ g₁₂ s₁₂)) :
  is_weq (pushout_of_maps po_f po_g u₁ u₂ u₃ s₁₂ s₁₃) :=
have acof_u₁ : is_acof u₁ := ⟨hcu₁, hwu₁⟩,
have acof_u₃ : is_acof u₃ := ⟨hcu₃, hwu₃⟩,
let po₁₂ := pushout_by_cof f₁₂ u₁ hf₁₂,
    u₂' := po₁₂.map₀,
    u₂'' := po₁₂.is_pushout.induced u₂ g₁₂ s₁₂,
    u₄ := pushout_of_maps po_f po_g u₁ u₂ u₃ s₁₂ s₁₃,
    po₃₄ := pushout_by_cof f₃₄ u₃ (pushout_is_cof po_f hf₁₂),
    u₄' := po₃₄.map₀,
    u₄'' := po₃₄.is_pushout.induced u₄ g₃₄ (by simp) in
have acof_u₂' : is_acof u₂' := pushout_is_acof po₁₂.is_pushout.transpose acof_u₁,
have acof_u₄' : is_acof u₄' := pushout_is_acof po₃₄.is_pushout.transpose acof_u₃,
have acof_u₂'' : is_acof u₂'' := have _ := hwu₂, begin
  refine ⟨hcu₂'', category_with_weak_equivalences.weq_of_comp_weq_left acof_u₂'.2 _⟩,
  simpa using this
end,
let k := pushout_of_maps po₁₂.is_pushout po₃₄.is_pushout f₁₃ f₂₄ g₁₃ po_f.commutes s₁₃.symm in
suffices Is_pushout u₂'' k g₂₄ u₄'',
  by convert weq_comp acof_u₄'.2 (pushout_is_acof this acof_u₂'').2; simp,
have _ := Is_pushout_of_Is_pushout_of_Is_pushout po_f po₃₄.is_pushout,
have Is_pushout f₁₂ (u₁ ≫ g₁₃) (u₂' ≫ k) po₃₄.map₁ := begin
  convert this using 1,
  { exact s₁₃.symm },
  { simp }
end,
have Is_pushout po₁₂.map₁ g₁₃ k po₃₄.map₁ :=
  Is_pushout_of_Is_pushout_of_Is_pushout' po₁₂.is_pushout this (by simp),
have po_g' : Is_pushout (po₁₂.map₁ ≫ u₂'') g₁₃ g₂₄ (po₃₄.map₁ ≫ u₄'') := by convert po_g using 1; simp,
Is_pushout_of_Is_pushout_of_Is_pushout_vert' this po_g' $
  by apply po₁₂.is_pushout.uniqueness; rw [←category.assoc, ←category.assoc]; simp [po_g.commutes]

lemma gluing_weq : is_weq (pushout_of_maps po_f po_g u₁ u₂ u₃ s₁₂ s₁₃) :=
let ⟨c₁⟩ := exists_brown_factorization ha₁ hb₁ u₁,
    ⟨c₂, h₁₂, hv₂, hr₂, hw₂, x, y⟩ :=
      exists_relative_brown_factorization
        ha₁ hb₁ (cofibrant_of_cof ha₁ hf₁₂) (cofibrant_of_cof hb₁ hg₁₂) u₁ u₂ f₁₂ g₁₂ s₁₂.symm c₁,
    ⟨c₃, h₁₃, hv₃, hr₃, hw₃, _, _⟩ :=
      exists_relative_brown_factorization ha₁ hb₁ ha₃ hb₃ u₁ u₃ f₁₃ g₁₃ s₁₃.symm c₁,
    po := pushout_by_cof c₁.f' f₁₂ c₁.hf' in
have cof_h₁₂ : is_cof h₁₂ := begin
  convert cof_comp (pushout_is_cof po.is_pushout.transpose hf₁₂) (x hg₁₂) using 1,
  simp
end,
have wv : _ := gluing_weq_aux po_f (pushout_by_cof h₁₂ h₁₃ cof_h₁₂).is_pushout hf₁₂
  (c₁.weq_f' hwu₁) (c₂.weq_f' hwu₂) (c₃.weq_f' hwu₃) hv₂.symm hv₃.symm c₁.hf' c₃.hf'
  (by rw ←Is_pushout.transpose_induced; exact cof_comp (cof_iso _) (x hg₁₂)),
have ww : _ := gluing_weq_aux po_g (pushout_by_cof h₁₂ h₁₃ cof_h₁₂).is_pushout hg₁₂
  c₁.hs.2 c₂.hs.2 c₃.hs.2 hw₂.symm hw₃.symm c₁.hs.1 c₃.hs.1
  (by rw ←Is_pushout.transpose_induced; exact cof_comp (cof_iso _) (y hf₁₂).1),
let po_h := pushout_by_cof h₁₂ h₁₃ cof_h₁₂ in
have wr : is_weq (pushout_of_maps po_h.is_pushout po_g c₁.r c₂.r c₃.r hr₂.symm hr₃.symm), begin
  refine (weq_iff_weq_inv _).mp ww,
  rw ←pushout_of_maps_comp,
  convert pushout_of_maps_id po_g,
  { exact c₁.hsr }, { exact c₂.hsr }, { exact c₃.hsr }
end,
begin
  convert weq_comp wv wr,
  rw ←pushout_of_maps_comp,
  congr,
  { exact c₁.hf'r.symm }, { exact c₂.hf'r.symm}, { exact c₃.hf'r.symm }
end

end homotopy_theory.cofibrations
