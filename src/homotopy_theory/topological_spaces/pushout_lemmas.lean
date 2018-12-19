import .colimits
import .homeomorphism
import .quotient_space
import .sierpinski
import .subspace
import category_theory.pasting_pushouts
import for_mathlib.analysis_topology_continuity

/-

We prove the following facts about pushouts in Top. Suppose given a
pushout square

      f
    A → B
  i ↓   ↓ j
    X → Y
      g

0. A subset of Y is closed (open) iff its preimages under g and j are.
1. If i is injective, then so is j.
2. If i is an embedding, then so is j.
3. If the image of i is closed (open), then so is the image of j.
4. In either case of 3, g : X → Y restricts to a homeomorphism
   g' : X - im i → Y - im j. Consequently, if k : C → X is another
   embedding whose image does not intersect the image of i, then
   g ∘ k is also an embedding.

In particular, we conclude that if i is a closed embedding, then so is
j, and in this case g induces a homeomorphism X - A → Y - B.

-/

open set

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{u}

section
parameters {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
parameter (po : Is_pushout i f g j)
include po

def is_open_in_pushout (s : set Y) : is_open s ↔ is_open (g ⁻¹' s) ∧ is_open (j ⁻¹' s) :=
⟨λ hs, ⟨g.property s hs, j.property s hs⟩, λ ⟨gs, js⟩, begin
   let xs := (opens_equiv X) ⟨g ⁻¹' s, gs⟩,
   let bs := (opens_equiv B) ⟨j ⁻¹' s, js⟩,
   let ys := po.induced xs bs
     (by ext a; change (i ≫ g) a ∈ s ↔ (f ≫ j) a ∈ s; rw po.commutes),
   convert ((opens_equiv Y).symm ys).property,
   rw [←equiv.apply_eq_iff_eq (set_equiv Y), ←forget_open_map, equiv.apply_inverse_apply],
   apply po.uniqueness; { rw [set_equiv_nat, ←category.assoc], simp, refl }
 end⟩

def is_closed_in_pushout (s : set Y) : is_closed s ↔ is_closed (g ⁻¹' s) ∧ is_closed (j ⁻¹' s) :=
is_open_in_pushout (-s)

end

-- For facts 1 & 2, the strategy is to show that injections
-- (respectively, embeddings) are precisely the maps with the left
-- lifting property with respect to the indiscrete two-point space
-- (respectively, also the Sierpinski space) and then use the fact
-- that such a left lifting property is preserved by pushouts.

section llp
-- TODO: Generalize/merge this with left lifting property

def llp_obj {A X : Top} (i : A ⟶ X) (Z : Top) : Prop :=
∀ (h : A ⟶ Z), ∃ (l : X ⟶ Z), i ≫ l = h

lemma llp_of_pushout {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
  (po : Is_pushout i f g j) (Z : Top) (hf : llp_obj i Z) : llp_obj j Z :=
begin
  intro h,
  rcases hf (f ≫ h) with ⟨l, hl⟩,
  refine ⟨po.induced l h hl, _⟩,
  simp
end

end llp

namespace pushout_lemmas_private
section
parameters {A X : Top} {i : A ⟶ X}

-- TODO: Might be able to simplify these next two results using lemmas
-- from sierpinski.lean

lemma injective_iff_llp : function.injective i ↔ llp_obj i prop_indisc :=
begin
  split; intro H,
  { intro h,
    -- Extend h : A → Prop by false to all of X.
    use ⟨λ x, ulift.up (∃ a, (h a).down ∧ i a = x), continuous_bot⟩,
    ext a,
    split; intro H',
    { rcases H' with ⟨a', ha', haa'⟩,
      have : a' = a, from H haa',
      rwa ←this },
    { exact ⟨a, H', rfl⟩ } },
  { intros a a' haa',
    -- Use lifting property to extend (λ x, x = a') to X.
    rcases H ⟨λ x, ulift.up (x = a'), continuous_bot⟩ with ⟨l, hl⟩,
    have := Top.hom_congr hl a,
    change l (i a) = _ at this,
    rw haa' at this,
    change (l ∘ i) a' = _ at this,
    rw hl at this,
    replace := congr_arg ulift.down this,
    change (a' = a') = (a = a') at this,
    rw ←iff_eq_eq at this,
    simpa using this }
end

lemma induced_iff_llp : (A.str = X.str.induced i) ↔ llp_obj i sierpinski :=
begin
  split; intro H,
  { intro h,
    -- Idea: h : A → Zind encodes an open set of A. By definition of
    -- the induced topology, this open set is the preimage of an open
    -- set of X, which defines a map X → Zind extending h.
    let u : set A := {a | (h a).down},
    have : is_open u := continuous_Prop.mp (by continuity),
    rcases is_open_induced_iff.mp (by convert ←this) with ⟨w, wo, uw⟩,
    refine ⟨⟨λ x, ulift.up (w x), continuous.comp (continuous_Prop.mpr wo) continuous_up⟩, _⟩,
    ext a,
    change _ ↔ u a,
    rw uw,
    exact iff.rfl },
  { -- One inequality is automatic because i is continuous.
    refine le_antisymm _ (continuous_iff_induced_le.mp i.property),
    intros w wo,
    -- Now we reverse the above argument. u defines a continuous map A → Zind,
    -- which we extend to X using the lifting property to express u as the
    -- preimage of an open set of X.
    rcases H ⟨λ x, ulift.up (w x), continuous.comp (continuous_Prop.mpr wo) continuous_up⟩
      with ⟨l, hl⟩,
    apply is_open_induced_iff.mpr,
    use {x | (l x).down},
    refine ⟨continuous_Prop.mp (by continuity), _⟩,
    funext a,
    exact (congr_arg ulift.down (Top.hom_congr hl a)).symm }
end

end
end pushout_lemmas_private

section
parameters {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
parameter (po : Is_pushout i f g j)
include po

lemma injective_j_of_injective_i (h : function.injective i) : function.injective j :=
begin
  rw pushout_lemmas_private.injective_iff_llp at ⊢ h,
  exact llp_of_pushout po _ h
end

lemma embedding_j_of_embedding_i (h : embedding i) : embedding j :=
⟨injective_j_of_injective_i h.1,
 begin
   have := h.2,
   erw pushout_lemmas_private.induced_iff_llp at ⊢ this,
   exact llp_of_pushout po _ this
 end⟩

end

namespace pushout_lemmas_private
section
parameters {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
parameter (po : Is_pushout i f g j)

/-
  Form the pushouts

               f
   A ⟶ *     A → B → *
  i↓   ↓a   i↓  j↓   ↓b
   X → X/A,  X → Y → Y/B
     qX        g   qY

  The outer rectangle on the right is then also a pushout, so
  comparison of these pushout squares yields a homeomorphism
  h : X/A ≅ Y/B carrying a to b.
-/


@[reducible] def YmodB := quotient_space j
local notation `Y/B` := YmodB
def qY : Y ⟶ Y/B := quotient_space.map j
def ptY : Y/B := quotient_space.pt j
def b : * ⟶ Y/B := Top.mk_hom (λ _, ptY) (by continuity)

def poY : Is_pushout j (Top.point_induced B) qY b := quotient_space.is_pushout j
def po' : Is_pushout i (Top.point_induced A) (qY ∘ g) b :=
Is_pushout_of_Is_pushout_of_Is_pushout po poY

@[reducible] def XmodA := quotient_space i
local notation `X/A` := XmodA
def qX : X ⟶ X/A := quotient_space.map i
def ptX : X/A := quotient_space.pt i
def a : * ⟶ X/A := Top.mk_hom (λ _, ptX) (by continuity)
def poX : Is_pushout i (Top.point_induced A) qX a := quotient_space.is_pushout i

def h : homeomorphism X/A Y/B := pushout.unique poX po'
lemma hab : h.hom ∘ a = b := by simp [h]
lemma hpt : h.hom ptX = ptY := Top.hom_congr hab punit.star
@[simp] lemma hpt' : h.hom ⁻¹' {ptY} = {ptX} :=
let h' := h.equiv in
begin
  ext p, simp [hpt.symm], change h' p = h' ptX ↔ p = ptX, simp
end

lemma pt_closed_iff : is_closed ({ptX} : set X/A) ↔ is_closed ({ptY} : set Y/B) :=
have _ := h.is_closed_iff ({ptY} : set Y/B),
by convert this.symm; rw [hpt']

lemma pt_open_iff : is_open ({ptX} : set X/A) ↔ is_open ({ptY} : set Y/B) :=
have _ := h.is_open_iff ({ptY} : set Y/B),
by convert this.symm; rw [hpt']

theorem range_i_closed_iff_range_j_closed : is_closed (range i) ↔ is_closed (range j) := calc
  is_closed (range i)
    ↔ is_closed ({ptX} : set X/A) : (quotient_space_pt_is_closed_iff i).symm
... ↔ is_closed ({ptY} : set Y/B) : pt_closed_iff
... ↔ is_closed (range j)         : quotient_space_pt_is_closed_iff j

theorem range_i_open_iff_range_j_open : is_open (range i) ↔ is_open (range j) := calc
  is_open (range i)
    ↔ is_open ({ptX} : set X/A) : (quotient_space_pt_is_open_iff i).symm
... ↔ is_open ({ptY} : set Y/B) : pt_open_iff
... ↔ is_open (range j)         : quotient_space_pt_is_open_iff j

-- Now we show that g : X → Y restricts to a homeomorphism g' : X - A → Y - B.

@[reducible] def XminusA := quotient_space.image_complement i
@[reducible] def XmodAminus := quotient_space.minus_base_point i
local notation `X-A` := XminusA
local notation `X/A₋` := XmodAminus

@[reducible] def YminusB := quotient_space.image_complement j
@[reducible] def YmodBminus := quotient_space.minus_base_point j
local notation `Y-B` := YminusB
local notation `Y/B₋` := YmodBminus

def h' : homeomorphism X/A₋ Y/B₋ :=
h.restrict $ calc
    _ = - {ptX}             : rfl
  ... = - (h.hom ⁻¹' {ptY}) : by rw hpt'
  ... = h.hom ⁻¹' (- {ptY}) : set.preimage_compl
  ... = _                   : rfl

local notation a ` ≅ ` b := homeomorphism a b

parameter (hyp : is_closed (range i) ∨ is_open (range i))

def hyp' : is_closed (range j) ∨ is_open (range j) :=
(or_congr range_i_closed_iff_range_j_closed range_i_open_iff_range_j_open).mp hyp

def g' : X-A ≅ Y-B :=
calc
  X-A ≅ X/A₋ : quotient_space.homeomorphism_complement i hyp
  ... ≅ Y/B₋ : h'
  ... ≅ Y-B  : (quotient_space.homeomorphism_complement j hyp').symm

lemma g'_g : incl _ ∘ g'.hom = g ∘ incl _ :=
rfl

parameters {C : Top} {k : C ⟶ X} (hk : embedding k) (hik : range i ∩ range k = ∅)

def k' : C ⟶ X-A :=
factor_through_incl k _ (subset_compl_comm.mp $ subset_compl_iff_disjoint.mpr hik)

theorem comp_embedding_of_embedding_of_disjoint : embedding (g ∘ k) :=
show embedding (incl _ ∘ g'.hom ∘ k'), from
have embedding k', from embedding_of_embedding_comp (incl _) hk,
embedding_compose this (embedding_compose g'.embedding (embedding_incl _))

end

end pushout_lemmas_private

export pushout_lemmas_private
  (range_i_open_iff_range_j_open range_i_closed_iff_range_j_closed
   comp_embedding_of_embedding_of_disjoint)

section
parameters {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
parameter (po : Is_pushout i f g j)
parameter (hyp : is_closed (range i) ∨ is_open (range i))

def complement_homeomorphism :
  quotient_space.image_complement i ≅ quotient_space.image_complement j :=
pushout_lemmas_private.g' po hyp

lemma complement_homeomorphism_eq :
  complement_homeomorphism.hom ≫ incl _ = incl _ ≫ g :=
pushout_lemmas_private.g'_g po hyp

end

end homotopy_theory.topological_spaces
