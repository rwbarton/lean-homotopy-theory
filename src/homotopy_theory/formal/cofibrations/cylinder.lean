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

end homotopy_theory.cofibrations
