import category_theory.assoc_pushouts
import category_theory.eq
import category_theory.groupoid
import category_theory.transport
import .homotopy

universes u v

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.weak_equivalences
open homotopy_theory.weak_equivalences.category_with_weak_equivalences
open precofibration_category cofibration_category

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
 by dsimp [cylinder_embedding.trans]; rw [assoc, m₁.e, m₀.e]⟩

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

structure homotopy_iso (t t' : homotopy hj f₀ f₁) :=
(k : t.c.ob ≅ t'.c.ob)
(hkii : ↑k ∘ t.c.ii = t'.c.ii)
(hpk : t'.c.p ∘ ↑k = t.c.p)
(e : t'.h.H ∘ ↑k = t.h.H)

lemma homotopy_equiv_of_iso {t t' : homotopy hj f₀ f₁} (i : homotopy_iso t t') :
  homotopy_equiv t t' :=
⟨t', ⟨⟨i.k, cof_iso _, i.hkii, i.hpk⟩, i.e⟩, homotopy_extension.refl t', ⟨⟩⟩

instance homotopy_equiv.setoid : setoid (homotopy hj f₀ f₁) :=
{ r := homotopy_equiv,
  iseqv :=
    ⟨λ t, homotopy_equiv.refl t,
     λ t₀ t₁, homotopy_equiv.symm,
     λ t₀ t₁ t₂, homotopy_equiv.trans⟩ }

variables (hj f₀ f₁)
def track := quotient (homotopy_equiv.setoid : setoid (homotopy hj f₀ f₁))

private noncomputable def chosen_cylinder : relative_cylinder hj :=
classical.choice (exists_relative_cylinder hj)

variables {hj f₀ f₁}
noncomputable def track.refl (f : b ⟶ x) : track hj f f :=
⟦⟨chosen_cylinder hj, homotopy_on.refl f⟩⟧

lemma track.refl_eq {f : b ⟶ x} (c : relative_cylinder hj) :
  (track.refl f : track hj f f) = ⟦⟨c, homotopy_on.refl f⟩⟧ :=
quot.sound $
  let c₀ := chosen_cylinder hj,
      ⟨⟨c', m₀, m₁⟩⟩ := exists_common_embedding c₀ c in
  ⟨⟨c', homotopy_on.refl f⟩,
   ⟨m₀, show f ∘ c'.p ∘ m₀.k = f ∘ c₀.p, by rw [←assoc, m₀.hpk]⟩,
   ⟨m₁, show f ∘ c'.p ∘ m₁.k = f ∘ c.p, by rw [←assoc, m₁.hpk]⟩, ⟨⟩⟩

local attribute [elab_with_expected_type] quotient.lift_on quotient.lift_on₂

def track.symm {f₀ f₁ : b ⟶ x} : track hj f₀ f₁ → track hj f₁ f₀ :=
λ t, quotient.lift_on t
  (λ t, ⟦⟨t.c.reverse, t.h.symm⟩⟧)
  (assume t t' ⟨t'', m₀, m₁, ⟨⟩⟩, quotient.sound $
    ⟨⟨t''.c.reverse, t''.h.symm⟩, ⟨m₀.m.reverse, m₀.e⟩, ⟨m₁.m.reverse, m₁.e⟩, ⟨⟩⟩)

def track.trans {f₀ f₁ f₂ : b ⟶ x} : track hj f₀ f₁ → track hj f₁ f₂ → track hj f₀ f₂ :=
λ t₀ t₁, quotient.lift_on₂ t₀ t₁
  (λ t₀ t₁, ⟦⟨t₀.c.glue t₁.c, t₀.h.trans t₁.h⟩⟧)
  (assume t₀ t₁ t₀' t₁' ⟨t₀'', m₀₀, m₀₁, ⟨⟩⟩ ⟨t₁'', m₁₀, m₁₁, ⟨⟩⟩, quotient.sound $
    ⟨⟨t₀''.c.glue t₁''.c, t₀''.h.trans t₁''.h⟩,
     ⟨m₀₀.m.glue m₁₀.m,
      begin
        apply (pushout_by_cof t₀.c.i₁ t₁.c.i₀ t₀.c.acof_i₁.1).is_pushout.uniqueness;
        dsimp [homotopy_on.trans, cylinder_embedding.glue]; rw ←assoc;
        simp [m₀₀.e, m₁₀.e],
      end⟩,
     ⟨m₀₁.m.glue m₁₁.m,
      begin
        apply (pushout_by_cof t₀'.c.i₁ t₁'.c.i₀ t₀'.c.acof_i₁.1).is_pushout.uniqueness;
        dsimp [homotopy_on.trans, cylinder_embedding.glue]; rw ←assoc;
        simp [m₀₁.e, m₁₁.e],
      end⟩, ⟨⟩⟩)

-- The groupoid laws.

lemma track.left_identity {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track.trans (track.refl _) t = t :=
quotient.induction_on t $ λ ⟨c₁, h⟩, quotient.sound $
  -- Set up variable names to match `exists_common_embedding` as
  -- closely as possible, so that what we construct is, in particular,
  -- a common embedding of c₀ and c₁.
  let c := chosen_cylinder hj,
      c₀ := c.glue c₁,
      p' : c₀.ob ⟶ c₁.ob :=
        (pushout_by_cof c.i₁ c₁.i₀ c.acof_i₁.1).is_pushout.induced
          (c₁.i₀ ∘ c.p) (𝟙 c₁.ob) (by rw [←assoc, c.pi₁]; simp),
      po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
      pp := po.is_pushout.induced p' (𝟙 c₁.ob) $ begin
        apply (pushout_by_cof j j hj).is_pushout.uniqueness,
        { rw [←assoc, ←assoc], change _ ∘ c₀.i₀ = _ ∘ c₁.i₀, simp,
          rw [←assoc, c.pi₀], simp },
        { rw [←assoc, ←assoc], change _ ∘ c₀.i₁ = _ ∘ c₁.i₁, simp }
      end,
      ⟨c'_ob, l, q', hl, hq', q'l⟩ := factorization pp,
      cem :=
        common_embedding_of_factorization c₀ c₁ po c'_ob l (c₁.p ∘ q')
          hl (weq_comp hq' c₁.hp) $ begin
            rw [←assoc, q'l],
            apply po.is_pushout.uniqueness; rw ←assoc; simp,
            apply (pushout_by_cof c.i₁ c₁.i₀ c.acof_i₁.1).is_pushout.uniqueness;
              rw ←assoc; simp; change _ = Is_pushout.induced _ _ _ _ ∘ _,
            { simp [c₁.pi₀] }, { simp },
          end,
      h' : homotopy_on cem.c' f₀ f₁ :=
        ⟨h.H ∘ q',
         calc
           h.H ∘ q' ∘ (l ∘ po.map₁ ∘ c₁.ii ∘ _)
             = h.H ∘ (q' ∘ l ∘ po.map₁) ∘ c₁.i₀  : by simp [relative_cylinder.i₀]
         ... = h.H ∘ c₁.i₀                       : by rw q'l; simp
         ... = f₀                                : h.Hi₀,
         calc
           h.H ∘ q' ∘ (l ∘ po.map₁ ∘ c₁.ii ∘ _)
             = h.H ∘ (q' ∘ l ∘ po.map₁) ∘ c₁.i₁  : by simp [relative_cylinder.i₁]
         ... = h.H ∘ c₁.i₁                       : by rw q'l; simp
         ... = f₁                                : h.Hi₁⟩ in
  ⟨⟨cem.c', h'⟩,
   ⟨cem.m₀, calc
      h.H ∘ q' ∘ (l ∘ po.map₀)
        = h.H ∘ ((q' ∘ l) ∘ po.map₀)  : by simp
    ... = h.H ∘ (pp ∘ po.map₀)        : by rw q'l
    ... = h.H ∘ p'                    : by simp
    ... = (homotopy_on.trans (homotopy_on.refl f₀) h).H  : begin
      unfold homotopy_on.trans homotopy_on.refl,
      apply (pushout_by_cof c.i₁ c₁.i₀ c.acof_i₁.1).is_pushout.uniqueness;
        rw ←assoc; simp [h.Hi₀]
    end⟩,
   ⟨cem.m₁, calc
      h.H ∘ q' ∘ (l ∘ po.map₁)
        = h.H ∘ ((q' ∘ l) ∘ po.map₁)  : by simp
    ... = h.H ∘ (pp ∘ po.map₁)        : by rw q'l
    ... = h.H                         : by simp⟩,
   ⟨⟩⟩

lemma track.left_inverse {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track.trans t.symm t = track.refl _ :=
quotient.induction_on t $ λ ⟨c, h⟩, quotient.sound $
  -- Set up variable names to match `exists_common_embedding` as
  -- closely as possible, so that what we construct is, in particular,
  -- a common embedding of c₀ and c₁.
  let c₁ := chosen_cylinder hj,
      c₀ := c.reverse.glue c,
      p' : c₀.ob ⟶ c.ob :=
        (pushout_by_cof c.reverse.i₁ c.i₀ c.reverse.acof_i₁.1).is_pushout.induced
          (𝟙 c.ob) (𝟙 c.ob) (by simp; erw comp_id), -- Yuck
      po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
      pp := po.is_pushout.induced p' (c.i₁ ∘ c₁.p) $ begin
        apply (pushout_by_cof j j hj).is_pushout.uniqueness;
          rw [←assoc, ←assoc],
        { change _ ∘ c₀.i₀ = _ ∘ c₁.i₀, simp,
          erw [←assoc, c₁.pi₀, comp_id], simp },
        { change _ ∘ c₀.i₁ = _ ∘ c₁.i₁, simp, rw [←assoc, c₁.pi₁], simp }
      end,
      ⟨c'_ob, l, q', hl, hq', q'l⟩ := factorization pp,
      cem :=
        common_embedding_of_factorization c₀ c₁ po c'_ob l (c.p ∘ q')
          hl (weq_comp hq' c.hp) $ begin
            rw [←assoc, q'l],
            apply po.is_pushout.uniqueness; rw ←assoc; simp,
            apply (pushout_by_cof c.reverse.i₁ c.i₀ c.reverse.acof_i₁.1).is_pushout.uniqueness;
              rw ←assoc; simp; change _ = Is_pushout.induced _ _ _ _ ∘ _,
            { erw [id_comp, Is_pushout.induced_commutes₀], refl },
            { simp },
            { simp [c.pi₁] }    -- What is this even for?
          end,
      h' : homotopy_on cem.c' f₁ f₁ :=
        ⟨h.H ∘ q',
         calc
           h.H ∘ q' ∘ (l ∘ po.map₁ ∘ c₁.ii ∘ _)
             = h.H ∘ (q' ∘ l ∘ po.map₁) ∘ c₁.i₀  : by simp [relative_cylinder.i₀]
         ... = h.H ∘ c.i₁ ∘ (c₁.p ∘ c₁.i₀)       : by rw q'l; simp
         ... = f₁                                : by rw [c₁.pi₀, h.Hi₁]; simp,
         calc
           h.H ∘ q' ∘ (l ∘ po.map₁ ∘ c₁.ii ∘ _)
             = h.H ∘ (q' ∘ l ∘ po.map₁) ∘ c₁.i₁  : by simp [relative_cylinder.i₁]
         ... = h.H ∘ c.i₁ ∘ (c₁.p ∘ c₁.i₁)       : by rw q'l; simp
         ... = f₁                                : by rw [c₁.pi₁, h.Hi₁]; simp⟩ in
  ⟨⟨cem.c', h'⟩,
   ⟨cem.m₀, calc
      h.H ∘ q' ∘ (l ∘ po.map₀)
        = h.H ∘ ((q' ∘ l) ∘ po.map₀)  : by simp
    ... = h.H ∘ (pp ∘ po.map₀)        : by rw q'l
    ... = h.H ∘ p'                    : by simp
    ... = (homotopy_on.trans h.symm h).H  : begin
      unfold homotopy_on.trans homotopy_on.symm,
      apply (pushout_by_cof c.reverse.i₁ c.i₀ c.reverse.acof_i₁.1).is_pushout.uniqueness;
        rw ←assoc; simp; erw id_comp
    end⟩,
   ⟨cem.m₁, calc
      h.H ∘ q' ∘ (l ∘ po.map₁)
        = h.H ∘ ((q' ∘ l) ∘ po.map₁)  : by simp
    ... = h.H ∘ (pp ∘ po.map₁)        : by rw q'l
    ... = h.H ∘ c.i₁ ∘ c₁.p           : by simp
    ... = (homotopy_on.refl f₁).H     : by rw h.Hi₁; refl⟩,
   ⟨⟩⟩

lemma track.inverse_inverse {f₀ f₁ : b ⟶ x} {t : track hj f₀ f₁} :
  t.symm.symm = t :=
-- t.symm.symm and t are homotopies defined on cylinder objects which
-- are equal, but not definitionally equal. Rather than dealing with
-- heterogeneous equality between the homotopies, it's easier to just
-- use `homotopy_equiv_of_iso`.
quotient.induction_on t $ λ t, quotient.sound $ homotopy_equiv_of_iso $
  ⟨iso.refl _,
   by apply (pushout_by_cof j j hj).is_pushout.uniqueness;
      dsimp [relative_cylinder.reverse, Is_pushout.swap];
      rw [←assoc, ←assoc, ←assoc]; simp,
   by dsimp [relative_cylinder.reverse]; simp,
   by simp [homotopy_on.symm]⟩

lemma track.right_inverse {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track.trans t t.symm = track.refl _ :=
by convert track.left_inverse t.symm; rw track.inverse_inverse

lemma track.assoc {f₀ f₁ f₂ f₃ : b ⟶ x}
  (t₀ : track hj f₀ f₁) (t₁ : track hj f₁ f₂) (t₂ : track hj f₂ f₃) :
  (t₀.trans t₁).trans t₂ = t₀.trans (t₁.trans t₂) :=
quotient.induction_on₃ t₀ t₁ t₂ $ λ t₀ t₁ t₂, quotient.sound $ homotopy_equiv_of_iso
  ⟨Is_pushout_assoc
     (pushout_by_cof t₀.c.i₁ t₁.c.i₀ t₀.c.acof_i₁.1).is_pushout
     (by convert (pushout_by_cof (t₀.c.glue t₁.c).i₁ t₂.c.i₀ _).is_pushout using 1; simp)
     (pushout_by_cof t₁.c.i₁ t₂.c.i₀ t₁.c.acof_i₁.1).is_pushout
     (by convert (pushout_by_cof t₀.c.i₁ (t₁.c.glue t₂.c).i₀ _).is_pushout using 1; simp),
   begin
     apply (pushout_by_cof j j hj).is_pushout.uniqueness; rw ←assoc,
     { change _ ∘ relative_cylinder.i₀ _ = relative_cylinder.i₀ _, simp },
     { change _ ∘ relative_cylinder.i₁ _ = relative_cylinder.i₁ _, simp }
   end,
   begin
     symmetry,
     apply Is_pushout_assoc_uniqueness;
       dsimp [relative_cylinder.glue]; simp
   end,
   begin
     symmetry,
     apply Is_pushout_assoc_uniqueness;
       dsimp [relative_cylinder.glue, homotopy_on.trans]; simp
   end⟩

lemma track.right_identity {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track.trans t (track.refl _) = t :=
calc
  t.trans (track.refl _)
    = t.trans (t.symm.trans t) : by rw track.left_inverse
... = (t.trans t.symm).trans t : by rw track.assoc
... = (track.refl _).trans t   : by rw track.right_inverse
... = t                        : by rw track.left_identity

section
variables (hj x)
include hj
def track_groupoid_rel := b ⟶ x
end

noncomputable instance : groupoid (track_groupoid_rel hj x) :=
{ hom := λ f₀ f₁, track hj f₀ f₁,
  id := λ f, track.refl f,
  comp := λ f₀ f₁ f₂ t₀ t₁, t₀.trans t₁,
  inv := λ f₀ f₁ t, t.symm,

  id_comp' := λ f₀ f₁, track.left_identity,
  comp_id' := λ f₀ f₁, track.right_identity,
  assoc' := λ f₀ f₁ f₂ f₃, track.assoc,
  inv_comp := λ f₀ f₁, track.left_inverse,
  comp_inv := λ f₀ f₁, track.right_inverse }

section functoriality

variables {y : C} (g : x ⟶ y)

def track.congr_left {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track hj (g ∘ f₀) (g ∘ f₁) :=
quotient.lift_on t
  (λ t, ⟦⟨t.c, t.h.congr_left hj g⟩⟧)
  (λ t t' ⟨t'', m₀, m₁, ⟨⟩⟩, quotient.sound
     ⟨⟨t''.c, t''.h.congr_left hj g⟩,
      ⟨m₀.m, show (g ∘ _) ∘ _ = _, by rw [←assoc, m₀.e]; refl⟩,
      ⟨m₁.m, show (g ∘ _) ∘ _ = _, by rw [←assoc, m₁.e]; refl⟩,
      ⟨⟩⟩)

noncomputable def track_groupoid_rel_functor {y} (g : x ⟶ y) :
  track_groupoid_rel hj x ↝ track_groupoid_rel hj y :=
{ obj := λ f, g ∘ f,
  map' := λ f₀ f₁ t, t.congr_left g,
  map_id' := λ f,
    show (track.refl f).congr_left g = track.refl (g ∘ f),
    begin
      apply congr_arg quotient.mk,
      unfold homotopy_on.refl homotopy_on.congr_left,
      congr' 2,
      rw ←assoc, refl
    end,
  map_comp' := λ f₀ f₁ f₂ t₀ t₁,
    show (t₀.trans t₁).congr_left g = (t₀.congr_left g).trans (t₁.congr_left g),
    begin
      induction t₀ using quot.ind,
      induction t₁ using quot.ind,
      apply congr_arg quotient.mk,
      congr', apply homotopy_on.ext,
      apply pushout_induced_comp
    end }

-- TODO: Precomposition is also a functor, & they are compatible,
-- interchange, etc.

end functoriality

-- We next relate tracks back to the original notion of "homotopies up
-- to homotopy", showing that for any particular relative cylinder
-- object c on a → b, tracks from f₀ : b → x to f₁ : b → x are in
-- one-to-one correspondence with homotopy classes rel b ⊔ₐ b → c of
-- homotopies from f₀ to f₁ defined on the given relative cylinder c,
-- provided that x is fibrant.

section track_homotopy_class
variables {c : relative_cylinder hj}
-- Use g₀ g₁ instead of f₀ f₁, so that we can put the variables in the
-- correct order (c first).
variables (hx : fibrant x)
variables {g₀ g₁ : b ⟶ x}

section correspondence

def homotopic_homotopies (h₀ h₁ : homotopy_on c g₀ g₁) : Prop :=
homotopic_rel c.hii h₀.H h₁.H

variables (c g₀ g₁)
instance homotopic_homotopies.setoid : setoid (homotopy_on c g₀ g₁) :=
{ r := homotopic_homotopies,
  iseqv :=
    ⟨λ h, homotopic_rel.refl _,
     λ h₀ h₁, homotopic_rel.symm,
     λ h₀ h₁ h₂, homotopic_rel.trans⟩ }

def homotopy_up_to_homotopy : Type v :=
quotient (homotopic_homotopies.setoid c g₀ g₁)

variables {c g₀ g₁}
-- One direction of the correspondence is easy.
def track_of_homotopy_on (h : homotopy_on c g₀ g₁) : track hj g₀ g₁ := ⟦⟨c, h⟩⟧

variables {x c g₀ g₁}
lemma eq_track_of_homotopic_rel (h₀ h₁ : homotopy_on c g₀ g₁) :
  homotopic_homotopies h₀ h₁ → track_of_homotopy_on h₀ = track_of_homotopy_on h₁ :=
assume ⟨c', ⟨⟨H, Hi₀, Hi₁⟩⟩⟩, quotient.sound $
  -- c' is a relative cylinder on b ⊔ₐ b → c. We can also view its
  -- underlying object as a relative cylinder on the original map a → b,
  -- and then H as a homotopy from g₀ to g₁ rel a → b.
  let c'' : relative_cylinder hj :=
        ⟨c'.ob, c'.i₀ ∘ c.ii, c.p ∘ c'.p,
         cof_comp c.hii c'.acof_i₀.1, weq_comp c'.hp c.hp, calc
           (c.p ∘ c'.p) ∘ (c'.i₀ ∘ c.ii)
             = c.p ∘ (c'.p ∘ c'.i₀) ∘ c.ii  : by simp
         ... = c.p ∘ c.ii                   : by rw c'.pi₀; simp
         ... = _                            : c.pii⟩ in
  ⟨⟨c'',
   ⟨H,
    show H ∘ (c'.i₀ ∘ c.ii ∘ _) = _, by simp [Hi₀]; rw ←assoc; exact h₀.Hi₀,
    show H ∘ (c'.i₀ ∘ c.ii ∘ _) = _, by simp [Hi₀]; rw ←assoc; exact h₀.Hi₁⟩⟩,
   ⟨⟨c'.i₀, c'.acof_i₀.1, rfl, by rw ←assoc; simp [c'.pi₀]⟩, Hi₀⟩,
   ⟨⟨c'.i₁, c'.acof_i₁.1, c'.ij.symm, by rw ←assoc; simp [c'.pi₁]⟩, Hi₁⟩, ⟨⟩⟩

local attribute [elab_with_expected_type] quotient.lift
def track_of_homotopy_class : homotopy_up_to_homotopy c g₀ g₁ → track hj g₀ g₁ :=
quotient.lift track_of_homotopy_on (λ h₀ h₁, eq_track_of_homotopic_rel h₀ h₁)

-- Similar to `homotopic_iff`. We choose a common embedding of c and
-- the cylinder on which t is defined, use the hypothesis that x is
-- fibrant to extend the homotopy to this new cylinder, and then
-- restrict it to c.
private def surj (t : track hj g₀ g₁) :
  ∃ h : homotopy_up_to_homotopy c g₀ g₁, track_of_homotopy_class h = t :=
quotient.induction_on t $ λ ⟨c', ⟨H, Hi₀, Hi₁⟩⟩,
  let ⟨⟨c'', m₀, m₁⟩⟩ := exists_common_embedding c c',
      ⟨H', hH'⟩ := fibrant_iff_rlp.mp hx m₁.acof_k H in
  ⟨⟦⟨H' ∘ m₀.k,
     by rw [←assoc, m₀.hki₀, ←m₁.hki₀, assoc, hH', Hi₀],
     by rw [←assoc, m₀.hki₁, ←m₁.hki₁, assoc, hH', Hi₁]⟩⟧,
   quotient.sound
     ⟨⟨c'',
      ⟨H',
       by rw [←m₁.hki₀, assoc, hH', Hi₀],
       by rw [←m₁.hki₁, assoc, hH', Hi₁]⟩⟩,
      ⟨m₀, rfl⟩, ⟨m₁, hH'⟩, ⟨⟩⟩⟩

set_option eqn_compiler.zeta true
private def inj (h₀ h₁ : homotopy_up_to_homotopy c g₀ g₁) :
  track_of_homotopy_class h₀ = track_of_homotopy_class h₁ → h₀ = h₁ :=
quotient.induction_on₂ h₀ h₁ $ λ h₀ h₁ e, quotient.sound $
  let ⟨t', m₀, m₁, ⟨⟩⟩ := quotient.exact e,
      c' := chosen_cylinder c.hii,
      po :=
        pushout_by_cof c'.ii
          ((pushout_by_cof c.ii c.ii c.hii).is_pushout.induced
            m₀.m.k m₁.m.k (by rw [m₀.m.hkii, m₁.m.hkii])) c'.hii,
      p' := po.is_pushout.induced (c.p ∘ c'.p) t'.c.p $ begin
         rw [←assoc, c'.pii],
         rw [pushout_induced_comp, pushout_induced_comp], congr' 1,
         { simp [m₀.m.hpk] }, { simp [m₁.m.hpk] }
      end,
      ⟨z, l, q, hl, hq, ql⟩ := factorization p' in
  have is_acof (l ∘ po.map₁), from
    ⟨cof_comp (pushout_is_cof po.is_pushout c'.hii) hl,
     weq_of_comp_weq_right hq (by convert t'.c.hp; simp [ql])⟩,
  let ⟨H', hH'⟩ := fibrant_iff_rlp.mp hx this t'.h.H in
  begin
    rw assoc at hH',
    refine ⟨c', ⟨⟨H' ∘ l ∘ po.map₀, _, _⟩⟩⟩;
    { change _ ∘ _ ∘ _ ∘ (_ ∘ _) = _, rw assoc,
      conv { to_lhs, congr, skip, rw ←assoc },
      rw po.is_pushout.commutes,
      simp [hH'], rw ←assoc, simp [m₀.e, m₁.e] }
  end

variables (c)
noncomputable def homotopy_class_equiv_track :
  homotopy_up_to_homotopy c g₀ g₁ ≃ track hj g₀ g₁ :=
equiv.of_bijective ⟨inj hx, surj hx⟩

section
variables (hj hx)
include hj c hx
def homotopy_class_groupoid := b ⟶ x
end

noncomputable instance homotopy_class_groupoid.groupoid :
  groupoid (homotopy_class_groupoid hj c hx) :=
transported_groupoid
  (by apply_instance : groupoid (track_groupoid_rel hj x))
  (λ g₀ g₁, (homotopy_class_equiv_track c hx).symm)

-- This is definitionally equal to .to_category of the above,
-- but helps with defining homotopy_class_functor somehow.
private noncomputable def homotopy_class_groupoid.category :
  category (homotopy_class_groupoid hj c hx) :=
transported_category
  (by apply_instance : category (track_groupoid_rel hj x))
  (λ g₀ g₁, (homotopy_class_equiv_track c hx).symm)

section functoriality
variables {c} {y : C} (hy : fibrant y) (k : x ⟶ y)
def homotopy_up_to_homotopy.congr_left {g₀ g₁ : b ⟶ x}
  (h : homotopy_up_to_homotopy c g₀ g₁) :
  homotopy_up_to_homotopy c (k ∘ g₀) (k ∘ g₁) :=
quotient.lift_on h
  (λ h, ⟦h.congr_left hj k⟧)
  (λ h h' H, quotient.sound (H.congr_left c.hii k))

noncomputable def homotopy_class_functor :
  homotopy_class_groupoid hj c hx ↝ homotopy_class_groupoid hj c hy :=
show @category_theory.functor
  _ (homotopy_class_groupoid.category c hx)
  _ (homotopy_class_groupoid.category c hy), from
transported_functor
  (λ g₀ g₁, (homotopy_class_equiv_track c hx).symm)
  (λ g₀ g₁, (homotopy_class_equiv_track c hy).symm)
  (track_groupoid_rel_functor k)

lemma homotopy_class_functor.obj {g : homotopy_class_groupoid hj c hx} :
  (homotopy_class_functor hx hy k : (homotopy_class_groupoid hj c _ ↝ _)) g = k ∘ g :=
rfl

lemma homotopy_class_functor.hom {g₀ g₁ : homotopy_class_groupoid hj c hx}
  {h : g₀ ⟶ g₁} : homotopy_class_functor hx hy k &> h = h.congr_left k :=
quotient.induction_on h $ λ h,
begin
  dsimp [homotopy_class_functor, transported_functor],
  rw equiv.apply_eq_iff_eq_inverse_apply,
  rw [equiv.symm_symm, equiv.symm_symm],
  refl
end

private lemma heq_of_homotopies_eq
  {g₀ g₀' g₁ g₁' : homotopy_class_groupoid hj c hx} (e₀ : g₀ = g₀') (e₁ : g₁ = g₁')
  (H : homotopy_on c g₀ g₁) (H' : homotopy_on c g₀' g₁') (e : H.H = H'.H) :
  (⟦H⟧ : g₀ ⟶ g₁) == (⟦H'⟧ : g₀' ⟶ g₁') :=
begin
  subst e₀, subst e₁,
  congr,
  cases H, cases H',
  congr,
  exact e
end

-- Next we show that homotopy_class_functor is functorial in "k".
lemma homotopy_class_functor.map_id :
  homotopy_class_functor hx hx (𝟙 x) = functor.id (homotopy_class_groupoid hj c hx) :=
begin
  fapply functor.hext,
  { intro g, rw [homotopy_class_functor.obj], simp },
  { intros g₀ g₁ h, rw homotopy_class_functor.hom,
    induction h using quot.ind,
    apply heq_of_homotopies_eq; { simp [homotopy_on.congr_left] } }
end

lemma homotopy_class_functor.map_comp {z : C} (hz : fibrant z) (k' : y ⟶ z) :
  (homotopy_class_functor hx hz (k' ∘ k) : homotopy_class_groupoid hj c hx ↝ _) =
  (homotopy_class_functor hx hy k).comp (homotopy_class_functor hy hz k') :=
begin
  fapply functor.hext,
  { intro g, rw [homotopy_class_functor.obj],
    rw [←assoc], refl },
  { intros g₀ g₁ h,
    rw [functor.comp_map],
    repeat { rw homotopy_class_functor.hom },
    induction h using quot.ind,
    apply heq_of_homotopies_eq hz;
    { simp [homotopy_class_functor.obj, homotopy_on.congr_left] } }
end

end functoriality

end correspondence
end track_homotopy_class

end homotopy_theory.cofibrations
