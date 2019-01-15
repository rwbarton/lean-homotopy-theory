import .arrow
import .cofibration_category
import tactic.slice

/- Brown factorization, aka "Ken Brown's lemma", and a relative version.
   Following Rădulescu-Banu, Cofibrations in Homotopy Theory, section 1.3. -/
   
universes v u

namespace homotopy_theory.cofibrations
open category_theory
open category_theory.category
open precofibration_category
open cofibration_category
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{v} C] [cofibration_category.{v} C]
  [has_initial_object.{v} C]
include cat

structure brown_factorization {a b : C} (f : a ⟶ b) : Type (max u v) :=
-- ab represents a coproduct of a and b, used to formulate the condition on f' + s
(ab : pushout (! a) (! b))
(b' : C)
(f' : a ⟶ b') (r : b' ⟶ b) (s : b ⟶ b')
(hf' : is_cof f')
(hf's : is_cof (ab.is_pushout.induced f' s (initial.uniqueness _ _)))
(hs : is_acof s)
(hf'r : f' ≫ r = f)
(hsr : s ≫ r = 𝟙 b)

lemma brown_factorization.hr {a b : C} {f : a ⟶ b} (c : brown_factorization f) :
  is_weq c.r :=
begin
  convert category_with_weak_equivalences.weq_of_comp_weq_left c.hs.2 _,
  rw c.hsr,
  apply weq_id
end

lemma brown_factorization.weq_f' {a b : C} {f : a ⟶ b} (c : brown_factorization f) (hf : is_weq f) :
  is_weq c.f' :=
begin
  convert category_with_weak_equivalences.weq_of_comp_weq_right c.hr _,
  rw c.hf'r,
  exact hf
end

--- Any map between cofibrant objects admits a Brown factorization (R-B, Lemma 1.3.1).
lemma exists_brown_factorization {a b : C} (ha : cofibrant a) (hb : cofibrant b) (f : a ⟶ b) :
  nonempty (brown_factorization f) :=
let ab := pushout_by_cof (! a) (! b) ha,
    ⟨b', j, g, hj, hg, hf⟩ :=
      factorization (ab.is_pushout.induced f (𝟙 b) (initial.uniqueness _ _)) in
⟨⟨ab, b', ab.map₀ ≫ j, g, ab.map₁ ≫ j,
  cof_comp (pushout_is_cof ab.is_pushout.transpose hb) hj,
  by convert hj; apply ab.is_pushout.uniqueness; simp,
  begin
    split,
    { refine cof_comp (pushout_is_cof ab.is_pushout ha) hj },
    { convert category_with_weak_equivalences.weq_of_comp_weq_right hg _,
      rw [assoc, hf], simpa using weq_id _ }
  end,
  by rw [assoc, hf]; simp,
  by rw [assoc, hf]; simp⟩⟩

--- R-B, Lemma 1.3.3
lemma relative_factorization {a₁ a₁' b₁ a₂ b₂ : C}
  (ha₁ : cofibrant a₁) (ha₂ : cofibrant a₂)
  (f₁' : a₁ ⟶ a₁') (r₁ : a₁' ⟶ b₁) (hf₁' : is_cof f₁') (hr : is_weq r₁)
  (f₂ : a₂ ⟶ b₂) (a : a₁ ⟶ a₂) (b : b₁ ⟶ b₂) (s : (f₁' ≫ r₁) ≫ b = a ≫ f₂) :
  ∃ a₂' (a' : a₁' ⟶ a₂') (f₂' : a₂ ⟶ a₂') (r₂ : a₂' ⟶ b₂)
  (hf' : f₁' ≫ a' = a ≫ f₂'), r₁ ≫ b = a' ≫ r₂ ∧ f₂' ≫ r₂ = f₂ ∧ is_cof f₂' ∧ is_weq r₂ ∧
  is_cof ((pushout_by_cof f₁' a hf₁').is_pushout.induced a' f₂' hf') :=
let po := pushout_by_cof f₁' a hf₁',
    g := po.is_pushout.induced (r₁ ≫ b) f₂ (by rw [←s, assoc]),
    ⟨a₂', s, r₂, hs, hr₂, hg⟩ := factorization g in
⟨a₂', po.map₀ ≫ s, po.map₁ ≫ s, r₂,
 by rw [←assoc, ←assoc, po.is_pushout.commutes],
 by rw [assoc, hg]; simp,
 by simp [hg],
 cof_comp (pushout_is_cof po.is_pushout hf₁') hs,
 hr₂,
 by convert hs; apply po.is_pushout.uniqueness; simp⟩

/-- R-B, Lemma 1.3.4. The statement there is missing hypotheses on the maps a and b,
  needed for the last two conclusions. -/
lemma exists_relative_brown_factorization {a₁ b₁ a₂ b₂ : C}
  (ha₁ : cofibrant a₁) (hb₁ : cofibrant b₁) (ha₂ : cofibrant a₂) (hb₂ : cofibrant b₂)
  (f₁ : a₁ ⟶ b₁) (f₂ : a₂ ⟶ b₂) (a : a₁ ⟶ a₂) (b : b₁ ⟶ b₂) (S : f₁ ≫ b = a ≫ f₂)
  (c₁ : brown_factorization f₁) : ∃ (c₂ : brown_factorization f₂) (b' : c₁.b' ⟶ c₂.b')
  (hf' : c₁.f' ≫ b' = a ≫ c₂.f') (hr : c₁.r ≫ b = b' ≫ c₂.r) (hs : c₁.s ≫ b' = b ≫ c₂.s),
  (is_cof b → is_cof ((pushout_by_cof c₁.f' a c₁.hf').is_pushout.induced b' c₂.f' hf')) ∧
  (is_cof a → is_acof ((pushout_by_cof c₁.s b c₁.hs.1).is_pushout.induced b' c₂.s hs)) :=
let po_a := pushout_by_cof c₁.f' a c₁.hf',
    a₃ := po_a.ob,
    f' := po_a.map₁,
    cof_f' : is_cof f' := pushout_is_cof po_a.is_pushout c₁.hf',
    po_b := pushout_by_cof c₁.s b c₁.hs.1,
    b₃ := po_b.ob,
    s := po_b.map₁,
    acof_s : is_acof s := pushout_is_acof po_b.is_pushout c₁.hs,
    r := po_b.is_pushout.induced (c₁.r ≫ b) (𝟙 _) (by rw [←assoc, c₁.hsr]; simp),
    f₃ : a₃ ⟶ b₃ := po_a.is_pushout.induced (c₁.r ≫ b ≫ s) (f₂ ≫ s) begin
      conv { to_rhs, rw [←assoc, ←S], rw [←c₁.hf'r, assoc] }, simp
    end,
    a₂b₂ := pushout_by_cof (! a₂) (! b₂) ha₂,
    -- TODO: lemma here?
    cof_a₃ : cofibrant a₃ := begin
      change is_cof _,
      convert cof_comp ha₂ (pushout_is_cof po_a.is_pushout c₁.hf'),
      apply initial.uniqueness
    end,
    cof_b₃ : cofibrant b₃ := begin
      change is_cof _,
      convert cof_comp hb₂ (pushout_is_cof po_b.is_pushout c₁.hs.1),
      apply initial.uniqueness
    end,
    a₃b₃ := pushout_by_cof (! a₃) (! b₃) cof_a₃,
    a₁_b₁ := c₁.ab.ob,
    cof_a₁_b₁ : cofibrant a₁_b₁ := begin
      change is_cof _,
      convert cof_comp hb₁ (pushout_is_cof c₁.ab.is_pushout ha₁),
      apply initial.uniqueness
    end,
    a₃_b₃ := a₃b₃.ob,
    cof_a₃_b₃ : cofibrant a₃_b₃ := begin
      change is_cof _,
      convert cof_comp cof_b₃ (pushout_is_cof a₃b₃.is_pushout cof_a₃),
      apply initial.uniqueness
    end,
    ⟨b₂', b', fs₃', r₃, hfs₃', hr₃, hf'sr, cof_fs₃', weq_r₃, cof_p⟩ := begin
      refine relative_factorization cof_a₁_b₁ cof_a₃_b₃ _ c₁.r c₁.hf's c₁.hr
        (a₃b₃.is_pushout.induced f₃ (𝟙 b₃) (initial.uniqueness _ _))
        (pushout_of_maps c₁.ab.is_pushout a₃b₃.is_pushout (𝟙 _) (a ≫ f') (b ≫ s)
          (initial.uniqueness _ _) (initial.uniqueness _ _))
        (b ≫ s) _,
      apply c₁.ab.is_pushout.uniqueness,
      { slice_lhs 1 2 { simp }, conv { to_lhs, rw [c₁.hf'r, S, assoc] },
        rw induced_pushout_of_maps, simp },
      { slice_lhs 1 2 { simp }, conv { to_lhs, rw [c₁.hsr, id_comp] },
        rw induced_pushout_of_maps, simp }
    end,
    f₃' := a₃b₃.map₀ ≫ fs₃',
    s₃ := a₃b₃.map₁ ≫ fs₃',
    f₂' := f' ≫ f₃',
    r₂ := r₃ ≫ r,
    s₂ := s ≫ s₃ in
have sr : s ≫ r = 𝟙 _, by simp,
have s₂r₂ : s₂ ≫ r₂ = 𝟙 _, begin
  slice_lhs 3 4 { rw hf'sr },
  slice_lhs 2 3 { rw Is_pushout.induced_commutes₁ },
  simp
end,
have weq_r₂ : is_weq r₂, begin
  refine weq_comp weq_r₃ _,
  rw ←weq_iff_weq_inv sr,
  exact acof_s.2
end,
⟨⟨a₂b₂, b₂', f₂', r₂, s₂,
  cof_comp (pushout_is_cof po_a.is_pushout c₁.hf')
    (cof_comp (pushout_is_cof a₃b₃.is_pushout.transpose cof_b₃) cof_fs₃'),
  begin
    have := cof_pushout cof_f' acof_s.1 a₂b₂.is_pushout
      (by convert a₃b₃.is_pushout; apply initial.uniqueness) (by apply initial.uniqueness),
    convert cof_comp this cof_fs₃',
    apply a₂b₂.is_pushout.uniqueness; conv { to_rhs, rw ←assoc }; simp
  end,
  begin
    refine ⟨_, (weq_iff_weq_inv s₂r₂).mpr weq_r₂⟩,
    exact cof_comp acof_s.1 (cof_comp (pushout_is_cof a₃b₃.is_pushout cof_a₃) cof_fs₃')
  end,
  begin
    slice_lhs 3 4 { rw hf'sr },
    slice_lhs 2 3 { rw Is_pushout.induced_commutes₀ },
    slice_lhs 1 2 { rw Is_pushout.induced_commutes₁ },
    simp [sr]
  end,
  s₂r₂⟩,
 b',
 begin
   convert congr_arg (λ z, c₁.ab.map₀ ≫ z) hfs₃' using 1,
   { slice_rhs 1 2 { rw Is_pushout.induced_commutes₀ } },
   { slice_rhs 1 2 { dsimp [pushout_of_maps], rw Is_pushout.induced_commutes₀ }, simp }
 end,
 begin
   have : c₁.r ≫ b = c₁.r ≫ b ≫ (s ≫ r), by rw [sr]; simp,
   rw this,
   slice_lhs 1 3 { rw hr₃ },
   simp
 end,
 begin
   convert congr_arg (λ z, c₁.ab.map₁ ≫ z) hfs₃' using 1,
   { slice_rhs 1 2 { rw Is_pushout.induced_commutes₁ } },
   { slice_rhs 1 2 { dsimp [pushout_of_maps], rw Is_pushout.induced_commutes₁ }, simp }
 end,
 begin
   intro hb,
   let v := _,
   let S₂ : cof_square v b' := ⟨_, _, _, _, cof_p⟩,
   let S₁ : cof_square a v,
   { refine ⟨c₁.ab.map₀, f' ≫ a₃b₃.map₀,
       by simp [v, pushout_of_maps], pushout_is_cof c₁.ab.is_pushout.transpose hb₁, _⟩,
     let po : pushout _ _ := _,
     change is_cof (po.is_pushout.induced _ _ _),
     have : is_cof (b ≫ s) := cof_comp hb acof_s.1,
     convert cof_pushout this cof_f'
       (Is_pushout_of_Is_pushout_of_Is_pushout c₁.ab.is_pushout.transpose po.is_pushout)
       (by convert a₃b₃.is_pushout.transpose; apply initial.uniqueness)
       (by apply initial.uniqueness) using 1,
     symmetry,
     apply pushout_induced_eq_iff; simp },
   have : c₁.f' = S₁.f₁ ≫ S₂.f₁, by simp,
   have S : is_cof_square a b' c₁.f' _ :=
     is_cof_square_comp ⟨S₁, rfl, rfl⟩ ⟨S₂, rfl, rfl⟩ this rfl,
   convert S.corner_cof.snd.snd,
   simp
 end,
 begin
   intro ha,
   let G := _,
   change is_acof G,
   suffices : is_cof G,
   { refine ⟨this, _⟩,
     have sG : s ≫ G = s₂, by simp,
     have : is_acof s := pushout_is_acof po_b.is_pushout c₁.hs,
     refine category_with_weak_equivalences.weq_of_comp_weq_left this.2 _,
     rw sG,
     exact (weq_iff_weq_inv s₂r₂).mpr weq_r₂ },
   -- From here on, the proof resembles the previous one
   let v := _,
   let S₂ : cof_square v b' := ⟨_, _, _, _, cof_p⟩,
   let S₁ : cof_square b v,
   { refine ⟨c₁.ab.map₁, s ≫ a₃b₃.map₁,
       by simp [v, pushout_of_maps], pushout_is_cof c₁.ab.is_pushout ha₁, _⟩,
     let po : pushout _ _ := _,
     change is_cof (po.is_pushout.induced _ _ _),
     have : is_cof (a ≫ f') := cof_comp ha cof_f',
     convert cof_pushout this acof_s.1
       (Is_pushout_of_Is_pushout_of_Is_pushout c₁.ab.is_pushout po.is_pushout)
       (by convert a₃b₃.is_pushout; apply initial.uniqueness)
       (by apply initial.uniqueness) using 1,
     symmetry,
     apply pushout_induced_eq_iff; simp },
   have : c₁.s = S₁.f₁ ≫ S₂.f₁, by simp,
   have S : is_cof_square b b' c₁.s _ :=
     is_cof_square_comp ⟨S₁, rfl, rfl⟩ ⟨S₂, rfl, rfl⟩ this rfl,
   convert S.corner_cof.snd.snd,
   simp
 end⟩

end homotopy_theory.cofibrations
