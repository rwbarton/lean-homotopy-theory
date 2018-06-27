import categories.pasting_pushouts
import homotopy_theory.formal.cylinder.definitions
import .cofibration_category

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder (endpoint)
open homotopy_theory.weak_equivalences
open homotopy_theory.weak_equivalences.category_with_weak_equivalences
open precofibration_category cofibration_category

variables {C : Type u} [cat : category.{u v} C] [cofibration_category.{u v} C]
include cat

variables {a b : C} {j : a ⟶ b} (hj : is_cof j)

structure relative_cylinder :=
(ob : C)
(ii : (pushout_by_cof j j hj).ob ⟶ ob)
(p : ob ⟶ b)
(hii : is_cof ii)
(hp : is_weq p)
(pii : p ∘ ii = (pushout_by_cof j j hj).is_pushout.induced (𝟙 b) (𝟙 b) rfl)

-- Any cofibration admits a relative cylinder.
lemma exists_relative_cylinder : nonempty (relative_cylinder hj) :=
let ⟨c, ii, p, hii, hp, pii⟩ :=
  factorization ((pushout_by_cof j j hj).is_pushout.induced (𝟙 b) (𝟙 b) rfl) in
⟨⟨c, ii, p, hii, hp, pii⟩⟩

variables {hj}

def relative_cylinder.i₀ (c : relative_cylinder hj) : b ⟶ c.ob :=
c.ii ∘ (pushout_by_cof j j hj).map₀

def relative_cylinder.i₁ (c : relative_cylinder hj) : b ⟶ c.ob :=
c.ii ∘ (pushout_by_cof j j hj).map₁

lemma relative_cylinder.pi₀ (c : relative_cylinder hj) : c.p ∘ c.i₀ = 𝟙 b :=
by unfold relative_cylinder.i₀; simp [c.pii]

lemma relative_cylinder.pi₁ (c : relative_cylinder hj) : c.p ∘ c.i₁ = 𝟙 b :=
by unfold relative_cylinder.i₁; simp [c.pii]

lemma relative_cylinder.ij (c : relative_cylinder hj) : c.i₀ ∘ j = c.i₁ ∘ j :=
begin
  unfold relative_cylinder.i₀ relative_cylinder.i₁,
  rw [←associativity, ←associativity, (pushout_by_cof j j hj).is_pushout.commutes]
end

lemma relative_cylinder.acof_i₀ (c : relative_cylinder hj) : is_acof c.i₀ :=
⟨cof_comp (pushout_is_cof (pushout_by_cof j j hj).is_pushout.transpose hj) c.hii,
 weq_of_comp_weq_right c.hp (by convert (weq_id _); exact c.pi₀)⟩

lemma relative_cylinder.acof_i₁ (c : relative_cylinder hj) : is_acof c.i₁ :=
⟨cof_comp (pushout_is_cof (pushout_by_cof j j hj).is_pushout hj) c.hii,
 weq_of_comp_weq_right c.hp (by convert (weq_id _); exact c.pi₁)⟩

structure cylinder_embedding (c c' : relative_cylinder hj) :=
(k : c.ob ⟶ c'.ob)
(hk : is_cof k)
(hkii : k ∘ c.ii = c'.ii)
(hpk : c'.p ∘ k = c.p)

lemma cylinder_embedding.hki₀ {c c' : relative_cylinder hj} (m : cylinder_embedding c c') :
  m.k ∘ c.i₀ = c'.i₀ :=
by unfold relative_cylinder.i₀; simp [m.hkii]

lemma cylinder_embedding.hki₁ {c c' : relative_cylinder hj} (m : cylinder_embedding c c') :
  m.k ∘ c.i₁ = c'.i₁ :=
by unfold relative_cylinder.i₁; simp [m.hkii]

lemma cylinder_embedding.acof_k {c c' : relative_cylinder hj} (m : cylinder_embedding c c') :
  is_acof m.k :=
⟨m.hk, weq_of_comp_weq_right c'.hp (by convert c.hp; rw m.hpk)⟩

-- Any two relative cylinders on the same cofibration can be embedded
-- in a third.
lemma exists_common_embedding (c₀ c₁ : relative_cylinder hj) :
  ∃ c' (m₀ : cylinder_embedding c₀ c') (m₁ : cylinder_embedding c₁ c'), true :=
let po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
    pp := po.is_pushout.induced c₀.p c₁.p (by rw [c₀.pii, c₁.pii]),
    ⟨c'_ob, l, q, hl, hq, ql⟩ := factorization pp in
let c' : relative_cylinder hj :=
  ⟨c'_ob, l ∘ po.map₁ ∘ c₁.ii, q,
   cof_comp c₁.hii (cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl),
   hq, by simp [ql, c₁.pii]⟩ in
⟨c',
 ⟨l ∘ po.map₀,
  cof_comp (pushout_is_cof po.is_pushout.transpose c₁.hii) hl,
  by rw [←associativity, po.is_pushout.commutes, associativity],
  by simp [ql]⟩,
 ⟨l ∘ po.map₁,
  cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl,
  rfl,
  by simp [ql]⟩,
 trivial⟩

def relative_cylinder.reverse (c : relative_cylinder hj) : relative_cylinder hj :=
⟨c.ob,
 c.ii ∘ (pushout_by_cof j j hj).is_pushout.swap,
 c.p,
 cof_comp (cof_iso (pushout_by_cof j j hj).is_pushout.swap_iso) c.hii,
 c.hp,
 by simp [c.pii]⟩

@[simp] lemma relative_cylinder.reverse_i₀ {c : relative_cylinder hj} :
  c.reverse.i₀ = c.i₁ :=
show c.ii ∘ (pushout_by_cof j j hj).is_pushout.induced _ _ _ ∘ (pushout_by_cof j j hj).map₀ = _,
by rw [←associativity]; simp; refl

@[simp] lemma relative_cylinder.reverse_i₁ {c : relative_cylinder hj} :
  c.reverse.i₁ = c.i₀ :=
show c.ii ∘ (pushout_by_cof j j hj).is_pushout.induced _ _ _ ∘ (pushout_by_cof j j hj).map₁ = _,
by rw [←associativity]; simp; refl

def relative_cylinder.glue (c₀ c₁ : relative_cylinder hj) : relative_cylinder.{u v} hj :=
let po := pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1 in
⟨po.ob,
 (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) $
   by rw [←associativity, ←associativity, c₀.ij, ←c₁.ij]; simp [po.is_pushout.commutes],
 po.is_pushout.induced c₀.p c₁.p (by rw [c₀.pi₁, c₁.pi₀]),
 begin
   let po₀ := pushout_by_cof c₀.i₀ (pushout_by_cof j j hj).map₀ c₀.acof_i₀.1,
   let po₀' :=
     (Is_pushout_of_Is_pushout_of_Is_pushout
       (pushout_by_cof j j hj).is_pushout.transpose po₀.is_pushout.transpose).transpose,
   let f :=
     (pushout_by_cof j j hj).is_pushout.induced
       (po₀.map₀ ∘ c₀.i₁) (po₀.map₁ ∘ (pushout_by_cof j j hj).map₁)
       (by rw [←associativity, ←associativity, ←c₀.ij,
               ←(pushout_by_cof j j hj).is_pushout.commutes,
               associativity, associativity, po₀.is_pushout.commutes]),
   let po₁ : Is_pushout c₀.i₁ (pushout_by_cof j j hj).map₀ po₀.map₀ f :=
     Is_pushout_of_Is_pushout_of_Is_pushout_vert'
       (pushout_by_cof j j hj).is_pushout
       (begin convert po₀' using 1, { exact c₀.ij.symm }, { simp } end) (by simp),
   let g := po₁.induced po.map₀ (po.map₁ ∘ c₁.ii)
     (by rw ←associativity; exact po.is_pushout.commutes),
   let po₂ : Is_pushout f c₁.ii g po.map₁ :=
     Is_pushout_of_Is_pushout_of_Is_pushout' po₁ (by convert po.is_pushout; simp) (by simp),
   have : ∀ p,
     (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) p =
     g ∘ po₀.map₁ :=
   begin
     intro p, apply (pushout_by_cof j j hj).is_pushout.uniqueness,
     { rw [←associativity, ←po₀.is_pushout.commutes], simp },
     { rw ←associativity,
       have :
         po₀.map₁ ∘ (pushout_by_cof.{u v} j j hj).map₁ =
         f ∘ (pushout_by_cof.{u v} j j hj).map₁, by simp,
       rw this,
       rw [associativity, po₂.commutes, ←associativity],
       change _ = po.map₁ ∘ c₁.i₁, simp }
   end,
   rw this,
   exact cof_comp
     (pushout_is_cof po₀.is_pushout c₀.acof_i₀.1)
     (pushout_is_cof po₂.transpose c₁.hii)
 end,
 weq_of_comp_weq_left
   (pushout_is_acof po.is_pushout c₀.acof_i₁).2
   (by simpa using c₁.hp),
 begin
   apply (pushout_by_cof j j hj).is_pushout.uniqueness;
   { rw ←associativity, simp, rw [c₀.pi₀] <|> rw [c₁.pi₁] }
 end⟩

@[simp] lemma relative_cylinder.glue_i₀ {c₀ c₁ : relative_cylinder hj} :
  (c₀.glue c₁).i₀ = (pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1).map₀ ∘ c₀.i₀ :=
let po := pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1 in
show
  (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) _ ∘
    (pushout_by_cof j j hj).map₀ = _, by simp

@[simp] lemma relative_cylinder.glue_i₁ {c₀ c₁ : relative_cylinder hj} :
  (c₀.glue c₁).i₁ = (pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1).map₁ ∘ c₁.i₁ :=
let po := pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1 in
show
  (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) _ ∘
    (pushout_by_cof j j hj).map₁ = _, by simp

end homotopy_theory.cofibrations
