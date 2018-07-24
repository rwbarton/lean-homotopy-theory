import categories.assoc_pushouts
import categories.groupoid
import .homotopy

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.weak_equivalences
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
   ⟨m₀, show f ∘ c'.p ∘ m₀.k = f ∘ c₀.p, by rw [←associativity, m₀.hpk]⟩,
   ⟨m₁, show f ∘ c'.p ∘ m₁.k = f ∘ c.p, by rw [←associativity, m₁.hpk]⟩, ⟨⟩⟩

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
        dsimp [homotopy_on.trans, cylinder_embedding.glue]; rw ←associativity;
        simp [m₀₀.e, m₁₀.e],
      end⟩,
     ⟨m₀₁.m.glue m₁₁.m,
      begin
        apply (pushout_by_cof t₀'.c.i₁ t₁'.c.i₀ t₀'.c.acof_i₁.1).is_pushout.uniqueness;
        dsimp [homotopy_on.trans, cylinder_embedding.glue]; rw ←associativity;
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
          (c₁.i₀ ∘ c.p) (𝟙 c₁.ob) (by rw [←associativity, c.pi₁]; simp),
      po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
      pp := po.is_pushout.induced p' (𝟙 c₁.ob) $ begin
        apply (pushout_by_cof j j hj).is_pushout.uniqueness,
        { rw [←associativity, ←associativity], change _ ∘ c₀.i₀ = _ ∘ c₁.i₀, simp,
          rw [←associativity, c.pi₀], simp },
        { rw [←associativity, ←associativity], change _ ∘ c₀.i₁ = _ ∘ c₁.i₁, simp }
      end,
      ⟨c'_ob, l, q', hl, hq', q'l⟩ := factorization pp,
      cem :=
        common_embedding_of_factorization c₀ c₁ po c'_ob l (c₁.p ∘ q')
          hl (weq_comp hq' c₁.hp) $ begin
            rw [←associativity, q'l],
            apply po.is_pushout.uniqueness; rw ←associativity; simp,
            apply (pushout_by_cof c.i₁ c₁.i₀ c.acof_i₁.1).is_pushout.uniqueness;
              rw ←associativity; simp; change _ = Is_pushout.induced _ _ _ _ ∘ _,
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
        rw ←associativity; simp [h.Hi₀]
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
          (𝟙 c.ob) (𝟙 c.ob) (by simp; erw right_identity_lemma), -- Yuck
      po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
      pp := po.is_pushout.induced p' (c.i₁ ∘ c₁.p) $ begin
        apply (pushout_by_cof j j hj).is_pushout.uniqueness;
          rw [←associativity, ←associativity],
        { change _ ∘ c₀.i₀ = _ ∘ c₁.i₀, simp,
          erw [←associativity, c₁.pi₀, right_identity_lemma], simp },
        { change _ ∘ c₀.i₁ = _ ∘ c₁.i₁, simp, rw [←associativity, c₁.pi₁], simp }
      end,
      ⟨c'_ob, l, q', hl, hq', q'l⟩ := factorization pp,
      cem :=
        common_embedding_of_factorization c₀ c₁ po c'_ob l (c.p ∘ q')
          hl (weq_comp hq' c.hp) $ begin
            rw [←associativity, q'l],
            apply po.is_pushout.uniqueness; rw ←associativity; simp,
            apply (pushout_by_cof c.reverse.i₁ c.i₀ c.reverse.acof_i₁.1).is_pushout.uniqueness;
              rw ←associativity; simp; change _ = Is_pushout.induced _ _ _ _ ∘ _,
            { erw [left_identity_lemma, Is_pushout.induced_commutes₀], refl },
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
        rw ←associativity; simp; erw left_identity_lemma
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
  ⟨isomorphism.Isomorphism.refl _,
   by apply (pushout_by_cof j j hj).is_pushout.uniqueness;
      dsimp [relative_cylinder.reverse, Is_pushout.swap];
      rw [←associativity, ←associativity, ←associativity]; simp,
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
     apply (pushout_by_cof j j hj).is_pushout.uniqueness; rw ←associativity,
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

variables {y : C} (g : x ⟶ y)

def track.congr_left {f₀ f₁ : b ⟶ x} (t : track hj f₀ f₁) :
  track hj (g ∘ f₀) (g ∘ f₁) :=
quotient.lift_on t
  (λ t, ⟦⟨t.c, t.h.congr_left hj g⟩⟧)
  (λ t t' ⟨t'', m₀, m₁, ⟨⟩⟩, quotient.sound
     ⟨⟨t''.c, t''.h.congr_left hj g⟩,
      ⟨m₀.m, show (g ∘ _) ∘ _ = _, by rw [←associativity, m₀.e]; refl⟩,
      ⟨m₁.m, show (g ∘ _) ∘ _ = _, by rw [←associativity, m₁.e]; refl⟩,
      ⟨⟩⟩)

variables (hj x)
include hj
def track_groupoid_rel := b ⟶ x
omit hj

noncomputable instance : groupoid (track_groupoid_rel hj x) :=
{ Hom := λ f₀ f₁, track hj f₀ f₁,
  identity := λ f, track.refl f,
  compose := λ f₀ f₁ f₂ t₀ t₁, t₀.trans t₁,
  inverse := λ f₀ f₁ t, t.symm,

  left_identity := λ f₀ f₁, track.left_identity,
  right_identity := λ f₀ f₁, track.right_identity,
  associativity := λ f₀ f₁ f₂ f₃, track.assoc,
  left_inverse := λ f₀ f₁, track.left_inverse,
  right_inverse := λ f₀ f₁, track.right_inverse }

variables {x}
noncomputable def track_groupoid_rel_functor {y} (g : x ⟶ y) :
  track_groupoid_rel hj x ↝ track_groupoid_rel hj y :=
{ onObjects := λ f, g ∘ f,
  onMorphisms := λ f₀ f₁ t, t.congr_left g,
  identities := λ f,
    show (track.refl f).congr_left g = track.refl (g ∘ f),
    begin
      apply congr_arg quotient.mk,
      unfold homotopy_on.refl homotopy_on.congr_left,
      congr' 2,
      rw ←associativity, refl
    end,
  functoriality := λ f₀ f₁ f₂ t₀ t₁,
    show (t₀.trans t₁).congr_left g = (t₀.congr_left g).trans (t₁.congr_left g),
    begin
      induction t₀ using quot.ind,
      induction t₁ using quot.ind,
      apply congr_arg quotient.mk,
      congr', apply homotopy_on.ext,
      apply pushout_induced_comp
    end }

end homotopy_theory.cofibrations
