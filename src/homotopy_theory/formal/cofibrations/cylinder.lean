import category_theory.pasting_pushouts
import homotopy_theory.formal.cylinder.definitions
import .cofibration_category

universes u v

open category_theory
open category_theory.category
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
  rw [←assoc, ←assoc, (pushout_by_cof j j hj).is_pushout.commutes]
end

lemma relative_cylinder.acof_i₀ (c : relative_cylinder hj) : is_acof c.i₀ :=
⟨cof_comp (pushout_is_cof (pushout_by_cof j j hj).is_pushout.transpose hj) c.hii,
 weq_of_comp_weq_right c.hp (by convert (weq_id _); exact c.pi₀)⟩

lemma relative_cylinder.acof_i₁ (c : relative_cylinder hj) : is_acof c.i₁ :=
⟨cof_comp (pushout_is_cof (pushout_by_cof j j hj).is_pushout hj) c.hii,
 weq_of_comp_weq_right c.hp (by convert (weq_id _); exact c.pi₁)⟩

-- If j : a → b is an *acyclic* cofibration, then so is c.ii.
lemma relative_cylinder.acof_ii (c : relative_cylinder hj) (hj' : is_weq j) : is_acof c.ii :=
have is_acof (pushout_by_cof j j hj).map₁, from
  pushout_is_acof (pushout_by_cof j j hj).is_pushout ⟨hj, hj'⟩,
have is_weq ((pushout_by_cof j j hj).is_pushout.induced (𝟙 b) (𝟙 b) rfl), from
  weq_of_comp_weq_left this.2 (by convert weq_id b using 1; simp),
⟨c.hii, weq_of_comp_weq_right c.hp (by convert this; simp [c.pii])⟩

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

def cylinder_embedding.refl (c : relative_cylinder hj) : cylinder_embedding c c :=
⟨𝟙 c.ob, cof_id _, by simp, by simp⟩

def cylinder_embedding.trans {c₀ c₁ c₂ : relative_cylinder hj}
  (m₀ : cylinder_embedding c₀ c₁) (m₁ : cylinder_embedding c₁ c₂) : cylinder_embedding c₀ c₂ :=
⟨m₁.k ∘ m₀.k,
 cof_comp m₀.hk m₁.hk,
 by rw [←assoc, m₀.hkii, m₁.hkii],
 by rw [assoc, m₁.hpk, m₀.hpk]⟩

-- Any two relative cylinders on the same cofibration can be embedded
-- in a third.

structure common_embedding (c₀ c₁ : relative_cylinder hj) :=
(c' : relative_cylinder hj)
(m₀ : cylinder_embedding c₀ c')
(m₁ : cylinder_embedding c₁ c')

-- Factor out the second part of the construction of a common
-- embedding, since we will need to apply it to a particular form of
-- factorization later, when verifying the identity and inverse laws
-- for track composition.
def common_embedding_of_factorization (c₀ c₁ : relative_cylinder hj)
  (po : pushout c₀.ii c₁.ii) (c'_ob : C) (l : po.ob ⟶ c'_ob) (q : c'_ob ⟶ b)
  (hl : is_cof l) (hq : is_weq q)
  (ql : q ∘ l = po.is_pushout.induced c₀.p c₁.p (by simp [c₀.pii, c₁.pii])) :
  common_embedding c₀ c₁ :=
let c' : relative_cylinder hj :=
  ⟨c'_ob, l ∘ po.map₁ ∘ c₁.ii, q,
   cof_comp c₁.hii (cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl),
   hq, by simp [ql, c₁.pii]⟩ in
⟨c',
 ⟨l ∘ po.map₀,
  cof_comp (pushout_is_cof po.is_pushout.transpose c₁.hii) hl,
  by rw [←assoc, po.is_pushout.commutes, assoc],
  by simp [ql]⟩,
 ⟨l ∘ po.map₁,
  cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl,
  rfl,
  by simp [ql]⟩⟩

lemma exists_common_embedding (c₀ c₁ : relative_cylinder hj) :
  nonempty (common_embedding c₀ c₁) :=
let po := pushout_by_cof c₀.ii c₁.ii c₀.hii,
    pp := po.is_pushout.induced c₀.p c₁.p (by rw [c₀.pii, c₁.pii]),
    ⟨c'_ob, l, q, hl, hq, ql⟩ := factorization pp in
⟨common_embedding_of_factorization c₀ c₁ po c'_ob l q hl hq ql⟩

def cylinder_embedding.pushout {c c₀ c₁ : relative_cylinder hj}
  (m₀ : cylinder_embedding c c₀) (m₁ : cylinder_embedding c c₁) : relative_cylinder hj :=
⟨(pushout_by_cof m₀.k m₁.k m₀.hk).ob,
 (pushout_by_cof m₀.k m₁.k m₀.hk).map₁ ∘ c₁.ii,
 (pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout.induced c₀.p c₁.p
   (by rw [m₀.hpk, ←m₁.hpk]),
 cof_comp c₁.hii (pushout_is_cof (pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout m₀.hk),
 weq_of_comp_weq_left
   (pushout_is_acof (pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout m₀.acof_k).2
   (by convert c₁.hp; simp),
 by simp [c₁.pii]⟩

def cylinder_embedding.pushout.map₀ {c c₀ c₁ : relative_cylinder hj}
  (m₀ : cylinder_embedding c c₀) (m₁ : cylinder_embedding c c₁) :
  cylinder_embedding c₀ (cylinder_embedding.pushout m₀ m₁) :=
⟨(pushout_by_cof m₀.k m₁.k m₀.hk).map₀,
 pushout_is_cof (pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout.transpose m₁.hk,
 show
   (pushout_by_cof m₀.k m₁.k m₀.hk).map₀ ∘ c₀.ii =
   (pushout_by_cof m₀.k m₁.k m₀.hk).map₁ ∘ c₁.ii,
 begin
   rw [←m₀.hkii, ←m₁.hkii],
   simp [(pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout.commutes]
 end,
 show Is_pushout.induced _ _ _ _ ∘ _ = _, by simp⟩

def cylinder_embedding.pushout.map₁ {c c₀ c₁ : relative_cylinder hj}
  (m₀ : cylinder_embedding c c₀) (m₁ : cylinder_embedding c c₁) :
  cylinder_embedding c₁ (cylinder_embedding.pushout m₀ m₁) :=
⟨(pushout_by_cof m₀.k m₁.k m₀.hk).map₁,
 pushout_is_cof (pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout m₀.hk,
 rfl,
 show Is_pushout.induced _ _ _ _ ∘ _ = _, by simp⟩

def cylinder_embedding.pushout.is_pushout {c c₀ c₁ : relative_cylinder hj}
  (m₀ : cylinder_embedding c c₀) (m₁ : cylinder_embedding c c₁) :
  Is_pushout m₀.k m₁.k
    (cylinder_embedding.pushout.map₀ m₀ m₁).k
    (cylinder_embedding.pushout.map₁ m₀ m₁).k :=
(pushout_by_cof m₀.k m₁.k m₀.hk).is_pushout

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
by rw [←assoc]; simp; refl

@[simp] lemma relative_cylinder.reverse_i₁ {c : relative_cylinder hj} :
  c.reverse.i₁ = c.i₀ :=
show c.ii ∘ (pushout_by_cof j j hj).is_pushout.induced _ _ _ ∘ (pushout_by_cof j j hj).map₁ = _,
by rw [←assoc]; simp; refl

def cylinder_embedding.reverse {c c' : relative_cylinder hj}
  (m : cylinder_embedding c c') : cylinder_embedding c.reverse c'.reverse :=
⟨m.k, m.hk, show m.k ∘ (c.ii ∘ _) = c'.ii ∘ _, by simp [m.hkii], m.hpk⟩

-- TODO: Should really have this `pushout_by_cof` exposed somewhere
def relative_cylinder.glue (c₀ c₁ : relative_cylinder hj) : relative_cylinder.{u v} hj :=
let po := pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1 in
⟨po.ob,
 (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) $
   by rw [←assoc, ←assoc, c₀.ij, ←c₁.ij]; simp [po.is_pushout.commutes],
 po.is_pushout.induced c₀.p c₁.p (by rw [c₀.pi₁, c₁.pi₀]),
 begin
   let po₀ := pushout_by_cof c₀.i₀ (pushout_by_cof j j hj).map₀ c₀.acof_i₀.1,
   let po₀' :=
     (Is_pushout_of_Is_pushout_of_Is_pushout
       (pushout_by_cof j j hj).is_pushout.transpose po₀.is_pushout.transpose).transpose,
   let f :=
     (pushout_by_cof j j hj).is_pushout.induced
       (po₀.map₀ ∘ c₀.i₁) (po₀.map₁ ∘ (pushout_by_cof j j hj).map₁)
       (by rw [←assoc, ←assoc, ←c₀.ij,
               ←(pushout_by_cof j j hj).is_pushout.commutes,
               assoc, assoc, po₀.is_pushout.commutes]),
   let po₁ : Is_pushout c₀.i₁ (pushout_by_cof j j hj).map₀ po₀.map₀ f :=
     Is_pushout_of_Is_pushout_of_Is_pushout_vert'
       (pushout_by_cof j j hj).is_pushout
       (begin convert po₀' using 1, { exact c₀.ij.symm }, { simp } end) (by simp),
   let g := po₁.induced po.map₀ (po.map₁ ∘ c₁.ii)
     (by rw ←assoc; exact po.is_pushout.commutes),
   let po₂ : Is_pushout f c₁.ii g po.map₁ :=
     Is_pushout_of_Is_pushout_of_Is_pushout' po₁ (by convert po.is_pushout; simp) (by simp),
   have : ∀ p,
     (pushout_by_cof j j hj).is_pushout.induced (po.map₀ ∘ c₀.i₀) (po.map₁ ∘ c₁.i₁) p =
     g ∘ po₀.map₁ :=
   begin
     intro p, apply (pushout_by_cof j j hj).is_pushout.uniqueness,
     { rw [←assoc, ←po₀.is_pushout.commutes], simp },
     { rw ←assoc,
       have :
         po₀.map₁ ∘ (pushout_by_cof.{u v} j j hj).map₁ =
         f ∘ (pushout_by_cof.{u v} j j hj).map₁, by simp,
       rw this,
       rw [assoc, po₂.commutes, ←assoc],
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
   { rw ←assoc, simp, rw [c₀.pi₀] <|> rw [c₁.pi₁] }
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

def cylinder_embedding.glue {c₀ c₁ c₀' c₁' : relative_cylinder hj}
  (m₀ : cylinder_embedding c₀ c₀') (m₁ : cylinder_embedding c₁ c₁') :
  cylinder_embedding (c₀.glue c₁) (c₀'.glue c₁') :=
⟨(pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1).is_pushout.induced
   ((pushout_by_cof c₀'.i₁ c₁'.i₀ c₀'.acof_i₁.1).map₀ ∘ m₀.k)
   ((pushout_by_cof c₀'.i₁ c₁'.i₀ c₀'.acof_i₁.1).map₁ ∘ m₁.k)
   (by rw [←assoc, ←assoc, m₀.hki₁, m₁.hki₀];
       exact (pushout_by_cof c₀'.i₁ c₁'.i₀ c₀'.acof_i₁.1).is_pushout.commutes),
 begin
   apply cof_pushout m₀.hk m₁.hk,
   convert (pushout_by_cof c₀'.i₁ c₁'.i₀ c₀'.acof_i₁.1).is_pushout using 1,
   exact m₀.hki₁, exact m₁.hki₀
 end,
 begin
   apply (pushout_by_cof j j hj).is_pushout.uniqueness; rw ←assoc,
   { change _ ∘ (c₀.glue c₁).i₀ = (c₀'.glue c₁').i₀, simp [m₀.hki₀.symm] },
   { change _ ∘ (c₀.glue c₁).i₁ = (c₀'.glue c₁').i₁, simp [m₁.hki₁.symm] }
 end,
 begin
   apply (pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1).is_pushout.uniqueness; rw ←assoc;
   change Is_pushout.induced _ _ _ _ ∘ _ = Is_pushout.induced _ _ _ _ ∘ _;
   simp [m₀.hpk, m₁.hpk]
 end⟩

section pair_map
variables (hj)
variables {a' b' : C} {j' : a' ⟶ b'} (hj' : is_cof j')

include hj hj'
structure pair_map :=
(g : a ⟶ a')
(h : b ⟶ b')
(commutes : h ∘ j = j' ∘ g)
omit hj hj'

variables {hj hj'}
def endpoints_map (h : pair_map hj hj') :
  (pushout_by_cof j j hj).ob ⟶ (pushout_by_cof j' j' hj').ob :=
pushout_of_maps
  (pushout_by_cof j j hj).is_pushout
  (pushout_by_cof j' j' hj').is_pushout
  h.g h.h h.h h.commutes h.commutes

-- Like `cylinder_embedding`, but we do not require that the map
-- between cylinders be a cofibration (since b → b' might not be one).
structure cylinder_map_over (h : pair_map hj hj')
  (c : relative_cylinder hj) (c' : relative_cylinder hj') :=
(k : c.ob ⟶ c'.ob)
(hkii : k ∘ c.ii = c'.ii ∘ endpoints_map h)
(hpk : c'.p ∘ k = h.h ∘ c.p)

lemma cylinder_map_over.hki₀ {h : pair_map hj hj'}
  {c : relative_cylinder hj} {c' : relative_cylinder hj'} (m : cylinder_map_over h c c') :
  m.k ∘ c.i₀ = c'.i₀ ∘ h.h :=
begin
  unfold relative_cylinder.i₀,
  rw [assoc, m.hkii],
  unfold endpoints_map pushout_of_maps,
  rw [←assoc], simp
end

lemma cylinder_map_over.hki₁ {h : pair_map hj hj'}
  {c : relative_cylinder hj} {c' : relative_cylinder hj'} (m : cylinder_map_over h c c') :
  m.k ∘ c.i₁ = c'.i₁ ∘ h.h :=
begin
  unfold relative_cylinder.i₁,
  rw [assoc, m.hkii],
  unfold endpoints_map pushout_of_maps,
  rw [←assoc], simp
end

lemma exists_of_pair_map (h : pair_map hj hj')
  (c₀ : relative_cylinder hj) (c₁ : relative_cylinder hj') :
  ∃ c' (m₀ : cylinder_map_over h c₀ c') (m₁ : cylinder_embedding c₁ c'), true :=
let po := pushout_by_cof c₀.ii (c₁.ii ∘ endpoints_map h) c₀.hii,
    pp := po.is_pushout.induced (h.h ∘ c₀.p) c₁.p $ begin
      rw [←assoc, c₀.pii, assoc, c₁.pii],
      unfold endpoints_map, rw [induced_pushout_of_maps, pushout_induced_comp],
      simp
    end,
    ⟨c'_ob, l, q, hl, hq, ql⟩ := factorization pp in
let c' : relative_cylinder hj' :=
  ⟨c'_ob, l ∘ po.map₁ ∘ c₁.ii, q,
   cof_comp c₁.hii (cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl),
   hq, by simp [ql, c₁.pii]⟩ in
⟨c',
 ⟨l ∘ po.map₀,
  by rw [←assoc, po.is_pushout.commutes]; simp,
  by simp [ql]⟩,
 ⟨l ∘ po.map₁,
  cof_comp (pushout_is_cof po.is_pushout c₀.hii) hl,
  rfl,
  by simp [ql]⟩,
 trivial⟩


end pair_map

end homotopy_theory.cofibrations
