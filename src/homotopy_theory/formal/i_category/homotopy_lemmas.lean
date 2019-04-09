import homotopy_theory.formal.cylinder.homotopy
import .definitions
import .lemmas

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder

namespace equiv_private
section
open category_theory.has_initial_object category_theory.preserves_initial_object
open category_theory.preserves_coproducts
open precofibration_category I_category

/-

Goal: If j : a → b is a cofibration, then homotopy rel j is an
equivalence relation. More generally, we will prove the
following. Suppose that G : Ia → x is a homotopy. In the diagram

  f₀  - f₁
  |
  f₀' - f₁'

suppose that f₀ ≃ f₀' rel j and that f₀ ≃ f₁ and f₀' ≃ f₁' via
homotopies that each restrict to G on a. Then f₁ ≃ f₁' rel j. By
taking G to be a constant homotopy, we conclude in particular that
homotopy rel j is an equivalence relation.

-/

parameters {C : Type u} [category.{v+1} C] [has_initial_object.{v} C]
  [has_coproducts.{v} C] [Icat : I_category.{v} C]
include Icat

parameters {a b : C} (j : a ⟶ b) (hj : is_cof j)
parameters {x : C} {f₀ f₀' f₁ f₁' : b ⟶ x}
parameters {G : I.obj a ⟶ x}
parameters {H₀ : homotopy f₀ f₀'} (h₀ : H₀.is_rel j)

-- Furthermore, we generalize over the direction of the homotopies
-- between f₀ and f₁ and between f₀' and f₁'.
parameters (ε : endpoint)
parameters {H : homotopy_dir ε f₀ f₁} (h : H.H ∘ I &> j = G)
parameters {H' : homotopy_dir ε f₀' f₁'} (h' : H'.H ∘ I &> j = G)
-- Goal: construct a homotopy from f₁ to f₂ rel j.

/-
  a ⊔ a →   Ia
    ↓       ↓
  b ⊔ b → b_Ia_b
-/

def Po : pushout (∂I &> j) (ii @> a) := pushout_by_cof _ _ (cof_coprod hj hj)
def b_Ia_b := Po.ob

-- I preserves the above pushout.
def Ipo : Is_pushout (I &> (∂I &> j)) (I &> (ii @> a)) (I &> Po.map₀) (I &> Po.map₁) :=
I_preserves_pushout_by_cof (cof_coprod hj hj) Po.is_pushout
-- Moreover, I(a ⊔ a) = Ia ⊔ Ia and I(b ⊔ b) = Ib ⊔ Ib.
def Ia_Ia : Is_coproduct (I &> (i₀ : a ⟶ a ⊔ a)) (I &> (i₁ : a ⟶ a ⊔ a)) :=
I_of_coprod_is_coproduct
def Ib_Ib : Is_coproduct (I &> (i₀ : b ⟶ b ⊔ b)) (I &> (i₁ : b ⟶ b ⊔ b)) :=
I_of_coprod_is_coproduct
-- Thus, we can "glue" the homotopies H and H' to form a map I(b ⊔ b) → X.
def HH' : I.obj (b ⊔ b) ⟶ x :=
Ib_Ib.induced H.H H'.H
-- Because the homotopies agree on a, the restriction of this map to I(a ⊔ a)
-- extends to a map I(Ia) → X. Then we get an induced map on I(b ⊔ₐ Ia ⊔ₐ b).
def GIp : I.obj (I.obj a) ⟶ x := G ∘ I &> (p @> a)

include h h'
def HH'' : I.obj b_Ia_b ⟶ x :=
Ipo.induced HH' GIp $
  -- This is a bit awful
  begin
    apply Ia_Ia.uniqueness;
    rw [←assoc, ←assoc, ←I.map_comp, ←I.map_comp];
    change
      _ ∘ I &> (coprod_of_maps j j ∘ _) =
      _ ∘ I &> (coprod.induced (i 0 @> a) (i 1 @> a) ∘ _);
    simp [HH', GIp]; rw h <|> rw h';
    rw [←assoc, ←I.map_comp]; simp
  end
omit h h'

-- The map guaranteed to be a cofibration by the relative cylinder axiom.
-- Induced map in same pushout square as above.
def j' := Po.is_pushout.induced (ii @> b) (I &> j) (ii.naturality _)

include h₀
lemma HH''iε : H₀.H ∘ j' = HH'' ∘ i ε @> _ :=
have t : ∀ {z} (k : z ⟶ _), H₀.H ∘ j' ∘ k = H₀.H ∘ (j' ∘ k), by simp,
begin
  unfold HH'' HH',
  apply Po.is_pushout.uniqueness,
  -- This is truly awful
  { rw i_nat_assoc,
    apply coprod.uniqueness;
    { simp, erw i_nat_assoc, simp,
      rw t, unfold j' ii, simp, rw ←assoc, simp,
      erw H₀.Hi₀ <|> erw H₀.Hi₁,
      erw H.Hiε <|> erw H'.Hiε } },
  { rw [i_nat_assoc, t], unfold j' GIp, simp,
    erw [←i_nat_assoc, ←h, ←i_nat_assoc, H.Hiε],
    exact h₀ }
end
omit h₀

-- Now we can apply the homotopy extension property of j'
lemma Ex_E : ∃ (E : I.obj (I.obj b) ⟶ x),
  E ∘ i ε @> (I.obj b) = H₀.H ∧ E ∘ I &> j' = HH'' :=
hep_cof j' (relative_cylinder j hj) ε _ _ _ HH''iε

section E
parameters (E : I.obj (I.obj b) ⟶ x)
  (hE : E ∘ i ε @> I.obj b = H₀.H ∧ E ∘ I &> j' = HH'')
-- Now E ∘ i ε.v is supposed to be a homotopy from f₁ to f₁' rel j.

include hE
lemma Eiεvi_ :
  E ∘ i ε.v @> I.obj b ∘ i 0 @> b = f₁ ∧
  E ∘ i ε.v @> I.obj b ∘ i 1 @> b = f₁' :=
have
  i.{v} ε.v @> I.obj b ∘ i 0 @> b = I &> j' ∘ I &> Po.map₀ ∘ i ε.v @> _ ∘ i₀ ∧
  i.{v} ε.v @> I.obj b ∘ i 1 @> b = I &> j' ∘ I &> Po.map₀ ∘ i ε.v @> _ ∘ i₁, begin
  split;
  { rw ←I.map_comp, unfold j', simp, erw i_nat_assoc,
    rw ←I.map_comp, dsimp [ii], simp,
    apply (i _).naturality }
end,
begin
  split;
  { rw ←assoc, rw this.1 <|> rw this.2,
    simp [hE.2, HH'', HH'],
    erw i_nat_assoc, dsimp, simp,
    -- dsimp: coprod vs (has_coproducts.coproduct _ _).ob?
    exact H.Hiεv <|> exact H'.Hiεv }
end

def Eiε : homotopy f₁ f₁' :=
{ H := E ∘ i ε.v @> I.obj b, Hi₀ := Eiεvi_.1, Hi₁ := Eiεvi_.2 }

lemma Eiε_is_rel : Eiε.is_rel j :=
have i ε.v @> I.obj b ∘ I &> j = I &> j' ∘ I &> Po.map₁ ∘ i ε.v @> I.obj a, begin
  rw ←I.map_comp, unfold j', simp,
  rw ←(i ε.v).naturality, refl
end,
begin
  dsimp [homotopy.is_rel, Eiε] { iota := tt },
  rw [←assoc, this], simp [hE.2, HH'', GIp],
  rw [←h, ←i_nat_assoc, ←i_nat_assoc, H.Hiεv]
end

end E

lemma f₁_f₂ : f₁ ≃ f₁' rel j :=
let ⟨E, hE⟩ := Ex_E in ⟨Eiε E hE, Eiε_is_rel E hE⟩

end
end equiv_private

end homotopy_theory.cofibrations

-- TODO: Is this a sensible place to put these?
namespace homotopy_theory.cylinder
open homotopy_theory.cofibrations

variables {C : Type u} [cat : category.{v+1} C]
  [has_initial_object.{v} C] [has_coproducts.{v} C] [I_category.{v} C]
include cat
variables {a b : C} {j : a ⟶ b} (hj : is_cof j)

lemma homotopic_rel.symm_trans {x : C} {f₀ f₁ f₂ : b ⟶ x} :
  f₀ ≃ f₁ rel j → f₀ ≃ f₂ rel j → f₁ ≃ f₂ rel j :=
assume ⟨H₁, h₁⟩ ⟨H₂, h₂⟩, equiv_private.f₁_f₂ j hj homotopy.refl_is_rel 0 h₁ h₂

lemma homotopic_rel.symm {x : C} {f₀ f₁ : b ⟶ x} (h : f₀ ≃ f₁ rel j) : f₁ ≃ f₀ rel j :=
homotopic_rel.symm_trans hj h (homotopic_rel.refl _)

lemma homotopic_rel.trans {x : C} {f₀ f₁ f₂ : b ⟶ x}
  (h₁ : f₀ ≃ f₁ rel j) (h₂ : f₁ ≃ f₂ rel j) : f₀ ≃ f₂ rel j :=
homotopic_rel.symm_trans hj (h₁.symm hj) h₂

lemma homotopic_rel_is_equivalence {x : C} :
  equivalence (homotopic_rel j : (b ⟶ x) → (b ⟶ x) → Prop) :=
⟨homotopic_rel.refl,
 λ f₀ f₁, homotopic_rel.symm hj,
 λ f₀ f₁ f₂, homotopic_rel.trans hj⟩

@[symm] lemma homotopic.symm {x : C} {f₀ f₁ : b ⟶ x} (h : f₀ ≃ f₁) : f₁ ≃ f₀ :=
begin
  rw ←(homotopic_rel_initial Ii_initial (! b)) at ⊢ h,
  exact homotopic_rel.symm (all_objects_cofibrant.cofibrant.{v} b) h,
end

@[trans] lemma homotopic.trans {x : C} {f₀ f₁ f₂ : b ⟶ x} (h₁ : f₀ ≃ f₁) (h₂ : f₁ ≃ f₂) : f₀ ≃ f₂ :=
begin
  rw ←(homotopic_rel_initial Ii_initial (! b)) at ⊢ h₁ h₂,
  exact homotopic_rel.trans (all_objects_cofibrant.cofibrant.{v} b) h₁ h₂,
end

lemma homotopic_is_equivalence {x : C} :
  equivalence (homotopic : (b ⟶ x) → (b ⟶ x) → Prop) :=
⟨homotopic.refl, λ f₀ f₁, homotopic.symm, λ f₀ f₁ f₂, homotopic.trans⟩

end homotopy_theory.cylinder
