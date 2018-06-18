import categories.congruence
import categories.preserves_colimits
import homotopy_theory.formal.cylinder.definitions
import homotopy_theory.formal.cylinder.hep
import homotopy_theory.formal.cylinder.homotopy
import homotopy_theory.formal.weak_equivalences.definitions
import .precofibration_category

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations

open homotopy_theory.cylinder

/-

An I-category [Baues, Algebraic homotopy, §I.3] is a precofibration
category C equipped with a cylinder functor satisfying the following
additional axioms.

* C has an initial object and every object of C is cofibrant.

  From the axioms of a precofibration category, it follows that C
  admits coproducts. Because we will need these coproducts in order to
  state a later axiom, we assume that C already comes equipped with a
  choice of coproducts in order to avoid non-definitionally equal
  instances.

* The cylinder functor I preserves pushouts by cofibrations and the
  initial object.

* Cofibrations have the two-sided HEP with respect to the cylinder I.

* The relative cylinder axiom: using the notation ∂I A = A ⊔ A, for
  each cofibration A → X, in the square

    ∂I A → I A
      ↓     ↓
    ∂I X → I X,

  the induced map from the pushout to I X is again a cofibration. (The
  pushout exists because ∂I A → ∂I X is a cofibration.)

* The cylinder I is equipped with an interchange structure.

-/

section

variables (C : Type u) [category.{u v} C] [has_initial_object.{u v} C] [has_coproducts.{u v} C]

class I_category extends has_cylinder C, preserves_initial_object (I : C ↝ C),
  precofibration_category C, all_objects_cofibrant.{u v} C,
  cylinder_has_interchange.{u v} C :=
(I_preserves_pushout_by_cof :
  Π {a b a' b'} {f : a ⟶ b} {g : a ⟶ a'} {f' : a' ⟶ b'} {g' : b ⟶ b'},
  is_cof f → Is_pushout f g g' f' → Is_pushout (I &> f) (I &> g) (I &> g') (I &> f'))
(hep_cof : ∀ {a b} (j : a ⟶ b), is_cof j → two_sided_hep j)
(relative_cylinder : ∀ {a b} (j : a ⟶ b) (hj : is_cof j), is_cof $
  (pushout_by_cof (∂I &> j) (ii @> a) (cof_coprod hj hj)).is_pushout.induced
    (ii @> b) (I &> j) (ii.naturality _))

end

namespace equiv_private
section
open categories.has_initial_object categories.preserves_initial_object
open categories.preserves_coproducts
open precofibration_category I_category

-- Goal: If j : a → b is a cofibration, then homotopy rel j is an
-- equivalence relation.
parameters {C : Type u} [category.{u v} C] [has_initial_object.{u v} C]
  [has_coproducts.{u v} C] [Icat : I_category.{u v} C]
include Icat

def Ii_initial : Is_initial_object.{u v} (I +> ∅ : C) :=
Is_initial_object_of_Is_initial_object.{u v} I
  (initial_object.{u v} C).is_initial_object

instance : preserves_coproducts (I : C ↝ C) :=
⟨λ a₀ a₁ b f₀ f₁ copr,
  let po : Is_pushout (! a₀) (! a₁) f₀ f₁ :=
    Is_pushout_of_Is_coproduct_of_Is_initial copr
      (initial_object.{u v} C).is_initial_object in
  Is_coproduct_of_Is_pushout_of_Is_initial
    (I_preserves_pushout_by_cof (all_objects_cofibrant.cofibrant a₀) po) Ii_initial⟩

parameters {a b : C} (j : a ⟶ b) (hj : is_cof j)
parameters {x : C} {f₀ f₁ f₂ : b ⟶ x}
parameters {H₁ : homotopy f₀ f₁} (h₁ : H₁.is_rel j)
parameters {H₂ : homotopy f₀ f₂} (h₂ : H₂.is_rel j)
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
Is_coproduct_of_Is_coproduct _
  (has_coproducts.coproduct.{u v} a a).is_coproduct
def Ib_Ib : Is_coproduct (I &> (i₀ : b ⟶ b ⊔ b)) (I &> (i₁ : b ⟶ b ⊔ b)) :=
Is_coproduct_of_Is_coproduct _
  (has_coproducts.coproduct.{u v} b b).is_coproduct
-- Thus, we can "glue" the homotopies H₁ and H₂ to form a map I(b ⊔ b) → X.
def H₁H₂ : I +> (b ⊔ b) ⟶ x :=
Ib_Ib.induced H₁.H H₂.H
-- Because the homotopies are rel j, the restriction of this map to I(a ⊔ a)
-- extends to a map I(Ia) → X. Then we get an induced map on I(b ⊔ₐ Ia ⊔ₐ b).
def f₀jpp : I +> I +> a ⟶ x := f₀ ∘ j ∘ p @> a ∘ I &> (p @> a)

include h₁ h₂
def H₁H₂' : I +> b_Ia_b ⟶ x :=
Ipo.induced H₁H₂ f₀jpp $
  -- This is a bit awful
  have ∀ ε, f₀ ∘ j ∘ p @> a = f₀ ∘ j ∘ p @> a ∘ I &> p @> a ∘ I &> i ε @> a := assume ε, calc
      f₀ ∘ j ∘ p @> a
        = (f₀ ∘ j ∘ p @> a) ∘ I &> (p @> a ∘ i ε @> a)  : by simp
    ... = f₀ ∘ j ∘ p @> a ∘ I &> p @> a ∘ I &> i ε @> a : by rw [I.functoriality]; simp,
  begin
    unfold homotopy.is_rel at h₁ h₂,
    apply Ia_Ia.uniqueness;
    rw [←associativity, ←associativity, ←I.functoriality, ←I.functoriality];
    change
      _ ∘ I &> (coprod_of_maps j j ∘ _) =
      _ ∘ I &> (coprod.induced (i 0 @> a) (i 1 @> a) ∘ _);
    simp [H₁H₂, f₀jpp]; rw h₁ <|> rw h₂; apply this
  end
omit h₁ h₂

-- The map guaranteed to be a cofibration by the relative cylinder axiom.
-- Induced map in same pushout square as above.
def j' := Po.is_pushout.induced (ii @> b) (I &> j) (ii.naturality _)

lemma i_nat_assoc (ε) {y z w : C} (g : I +> z ⟶ w) (h : y ⟶ z) :
  g ∘ (i ε) @> z ∘ h = g ∘ I &> h ∘ (i ε) @> y :=
by erw [←associativity, (i ε).naturality]; simp

lemma p_nat_assoc {y z w : C} (g : z ⟶ w) (h : y ⟶ z) :
  g ∘ p @> z ∘ I &> h = g ∘ h ∘ p @> y :=
by erw [←associativity, p.naturality]; simp

lemma H₁H₂'i0 : f₀ ∘ p @> b ∘ j' = H₁H₂' ∘ i 0 @> _ :=
have t : ∀ {z} (k : z ⟶ _), f₀ ∘ p @> b ∘ j' ∘ k = f₀ ∘ p @> b ∘ (j' ∘ k), by simp,
begin
  unfold homotopy.is_rel at h₁ h₂,
  unfold H₁H₂' H₁H₂,
  apply Po.is_pushout.uniqueness,
  -- This is truly awful
  { rw i_nat_assoc,
    apply coprod.uniqueness;
    { simp, erw i_nat_assoc, simp,
      rw t, unfold j' ii, simp, rw ←associativity, simp, rw ←associativity, simp,
      rw H₁.Hi₀ <|> rw H₂.Hi₀ } },
  { rw [i_nat_assoc, t], unfold j' f₀jpp, simp,
    rw [←i_nat_assoc, p_nat_assoc],
    have :
      f₀ ∘ j ∘ p @> a ∘ (i 0 @> a) ∘ p @> a =
      f₀ ∘ j ∘ (p @> a ∘ i 0 @> a) ∘ p @> a, by simp only [associativity],
    erw this, dsimp, simp }     -- dsimp rewrites 1 +> a to a in some type
end

-- Now we can apply the homotopy extension property of j'
lemma Ex_E : ∃ (E : I +> (I +> b) ⟶ x),
  E ∘ i 0 @> (I +> b) = f₀ ∘ p @> b ∧ E ∘ I &> j' = H₁H₂' :=
hep_cof j' (relative_cylinder j hj) 0 _ (f₀ ∘ p @> b) _ H₁H₂'i0

section E
parameters (E : I +> (I +> b) ⟶ x)
  (hE : E ∘ i 0 @> (I +> b) = f₀ ∘ p @> b ∧ E ∘ I &> j' = H₁H₂')
-- Now E ∘ i 1 is supposed to be a homotopy from f₁ to f₂ rel j.

include hE
lemma Ei1i_ :
  E ∘ i 1 @> (I +> b) ∘ i 0 @> b = f₁ ∧
  E ∘ i 1 @> (I +> b) ∘ i 1 @> b = f₂ :=
have
  i.{u v} 1 @> (I +> b) ∘ i 0 @> b = I &> j' ∘ I &> Po.map₀ ∘ i 1 @> _ ∘ i₀ ∧
  i.{u v} 1 @> (I +> b) ∘ i 1 @> b = I &> j' ∘ I &> Po.map₀ ∘ i 1 @> _ ∘ i₁, begin
  split;
  { rw ←I.functoriality, unfold j', simp, erw i_nat_assoc,
    rw ←I.functoriality, unfold ii, simp,
    apply (i _).naturality }
end,
begin
  split;
  { rw ←associativity, rw this.1 <|> rw this.2,
    simp [hE.2, H₁H₂', H₁H₂],
    erw i_nat_assoc, dsimp, simp,
    -- dsimp: coprod vs (has_coproducts.coproduct _ _).ob?
    exact H₁.Hi₁ <|> exact H₂.Hi₁ }
end

def Ei1 : homotopy f₁ f₂ :=
{ H := E ∘ i 1 @> (I +> b), Hi₀ := Ei1i_.1, Hi₁ := Ei1i_.2 }

local attribute [elab_simple] functor.Functor.onMorphisms
lemma Ei1_is_rel : Ei1.is_rel j :=
have i 1 @> (I +> b) ∘ I &> j = I &> j' ∘ I &> Po.map₁ ∘ _, begin
  rw ←I.functoriality, unfold j', simp,
  rw ←(i 1).naturality, refl
end,
have f₀j_f₁j : f₀ ∘ j = f₁ ∘ j := agree_of_is_rel h₁,
begin
  dsimp [homotopy.is_rel, Ei1] { iota := tt },
  rw [←associativity, this], simp [hE.2, H₁H₂', f₀jpp],
  rw f₀j_f₁j,
  rw ←i_nat_assoc, dsimp,
  have :
    f₁ ∘ j ∘ p @> a ∘ (i 1 @> a) ∘ p @> a =
    f₁ ∘ j ∘ (p @> a ∘ i 1 @> a) ∘ p @> a, by simp only [associativity],
  rw this, dsimp, simp
end

end E

lemma f₁_f₂ : f₁ ≃ f₂ rel j :=
let ⟨E, hE⟩ := Ex_E in ⟨Ei1 E hE, Ei1_is_rel E hE⟩

end
end equiv_private

end homotopy_theory.cofibrations

-- TODO: Is this a sensible place to put these?
namespace homotopy_theory.cylinder
open homotopy_theory.cofibrations

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat
variables {a b : C} {j : a ⟶ b} (hj : is_cof j)

lemma homotopic_rel.symm_trans {x : C} {f₀ f₁ f₂ : b ⟶ x} :
  (f₀ ≃ f₁ rel j) → (f₀ ≃ f₂ rel j) → (f₁ ≃ f₂ rel j) :=
assume ⟨H₁, h₁⟩ ⟨H₂, h₂⟩, equiv_private.f₁_f₂ j hj h₁ h₂

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

lemma homotopic.symm {x : C} {f₀ f₁ : b ⟶ x} (h : f₀ ≃ f₁) : f₁ ≃ f₀ :=
begin
  rw ←(homotopic_rel_initial (equiv_private.Ii_initial) (! b)) at ⊢ h,
  exact homotopic_rel.symm (all_objects_cofibrant.cofibrant.{u v} b) h,
end

lemma homotopic.trans {x : C} {f₀ f₁ f₂ : b ⟶ x} (h₁ : f₀ ≃ f₁) (h₂ : f₁ ≃ f₂) : f₀ ≃ f₂ :=
begin
  rw ←(homotopic_rel_initial (equiv_private.Ii_initial) (! b)) at ⊢ h₁ h₂,
  exact homotopic_rel.trans (all_objects_cofibrant.cofibrant.{u v} b) h₁ h₂,
end

lemma homotopic_is_equivalence {x : C} :
  equivalence (homotopic : (b ⟶ x) → (b ⟶ x) → Prop) :=
⟨homotopic.refl, λ f₀ f₁, homotopic.symm, λ f₀ f₁ f₂, homotopic.trans⟩

end homotopy_theory.cylinder

namespace homotopy_theory.cofibrations
-- Homotopy equivalences as the weak equivalences of an I-category.
open homotopy_theory.cylinder
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

variables (C)
def homotopy_congruence ⦃a b : C⦄ := (homotopic : (a ⟶ b) → (a ⟶ b) → Prop)
instance : congruence (homotopy_congruence C) :=
congruence.mk' (λ a b, homotopic_is_equivalence)
  (λ a b c f f' g, homotopic.congr_left g)
  (λ a b c f g g', homotopic.congr_right f)

instance homotopy_category.category_with_weak_equivalences :
  category_with_weak_equivalences (category_mod_congruence C (homotopy_congruence C)) :=
isomorphisms_as_weak_equivalences

instance I_category.category_with_weak_equivalences : category_with_weak_equivalences C :=
preimage_with_weak_equivalences (quotient_functor C (homotopy_congruence C))

end homotopy_theory.cofibrations
