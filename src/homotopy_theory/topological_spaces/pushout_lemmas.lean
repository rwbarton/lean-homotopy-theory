import .colimits
import .homeomorphism
import .quotient_space
import .subspace
import categories.pasting_pushouts

/-

We prove the following facts about pushouts in Top. Suppose given a
pushout square

      f
    A → B
  i ↓   ↓ j
    X → Y
      g

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

-- TODO: Facts 1 & 2

open set

open categories
open categories.isomorphism
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{u}

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
lemma hab : ↑h ∘ a = b := by simp [h]
lemma hpt : h ptX = ptY := Top.hom_congr hab punit.star
@[simp] lemma hpt' : h ⁻¹' {ptY} = {ptX} :=
let h' := h.equiv in
begin
  ext p, simp [hpt.symm], change h' p = h' ptX ↔ p = ptX, simp
end

lemma pt_closed_iff : is_closed ({ptX} : set X/A) ↔ is_closed ({ptY} : set Y/B) :=
have _ := h.is_closed_iff ({ptY} : set Y/B),
by convert this.symm; simp

lemma pt_open_iff : is_open ({ptX} : set X/A) ↔ is_open ({ptY} : set Y/B) :=
have _ := h.is_open_iff ({ptY} : set Y/B),
by convert this.symm; simp

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
    _ = - {ptX}         : rfl
  ... = - (h ⁻¹' {ptY}) : by rw hpt'
  ... = h ⁻¹' (- {ptY}) : set.preimage_compl
  ... = _               : rfl

local notation a ` ≅ ` b := homeomorphism a b

parameter (hyp : is_closed (range i) ∨ is_open (range i))

def hyp' : is_closed (range j) ∨ is_open (range j) :=
(or_congr range_i_closed_iff_range_j_closed range_i_open_iff_range_j_open).mp hyp

def g' : X-A ≅ Y-B :=
calc
  X-A ≅ X/A₋ : quotient_space.homeomorphism_complement i hyp
  ... ≅ Y/B₋ : h'
  ... ≅ Y-B  : (quotient_space.homeomorphism_complement j hyp').symm

lemma g'_g : incl _ ∘ g'.morphism = g ∘ incl _ :=
rfl

parameters {C : Top} {k : C ⟶ X} (hk : embedding k) (hik : range i ∩ range k = ∅)

def k' : C ⟶ X-A :=
factor_through_incl k _ (subset_compl_comm.mp $ subset_compl_iff_disjoint.mpr hik)

theorem comp_embedding_of_embedding_of_disjoint : embedding (g ∘ k) :=
show embedding (incl _ ∘ g'.morphism ∘ k'), from
have embedding k', from
  embedding_of_embedding_compose k'.property continuous_subtype_val hk,
embedding_compose this (embedding_compose g'.embedding (embedding_incl _))

end

end pushout_lemmas_private

-- TODO: g' also?
export pushout_lemmas_private
  (range_i_open_iff_range_j_open range_i_closed_iff_range_j_closed
   comp_embedding_of_embedding_of_disjoint)


end homotopy_theory.topological_spaces
