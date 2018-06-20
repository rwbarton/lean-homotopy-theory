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
parameters {x : C} {f₀ f₀' f₁ f₁' : b ⟶ x}
parameters {G : I +> a ⟶ x}
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
Is_coproduct_of_Is_coproduct _
  (has_coproducts.coproduct.{u v} a a).is_coproduct
def Ib_Ib : Is_coproduct (I &> (i₀ : b ⟶ b ⊔ b)) (I &> (i₁ : b ⟶ b ⊔ b)) :=
Is_coproduct_of_Is_coproduct _
  (has_coproducts.coproduct.{u v} b b).is_coproduct
-- Thus, we can "glue" the homotopies H and H' to form a map I(b ⊔ b) → X.
def HH' : I +> (b ⊔ b) ⟶ x :=
Ib_Ib.induced H.H H'.H
-- Because the homotopies agree on a, the restriction of this map to I(a ⊔ a)
-- extends to a map I(Ia) → X. Then we get an induced map on I(b ⊔ₐ Ia ⊔ₐ b).
def GIp : I +> I +> a ⟶ x := G ∘ I &> (p @> a)

include h h'
def HH'' : I +> b_Ia_b ⟶ x :=
Ipo.induced HH' GIp $
  -- This is a bit awful
  begin
    apply Ia_Ia.uniqueness;
    rw [←associativity, ←associativity, ←I.functoriality, ←I.functoriality];
    change
      _ ∘ I &> (coprod_of_maps j j ∘ _) =
      _ ∘ I &> (coprod.induced (i 0 @> a) (i 1 @> a) ∘ _);
    simp [HH', GIp]; rw h <|> rw h';
    rw [←associativity, ←I.functoriality]; simp
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
      rw t, unfold j' ii, simp, rw ←associativity, simp,
      rw H₀.Hi₀ <|> rw H₀.Hi₁,
      rw H.Hiε <|> rw H'.Hiε } },
  { rw [i_nat_assoc, t], unfold j' GIp, simp,
    rw [←i_nat_assoc, ←h, ←i_nat_assoc, H.Hiε],
    exact h₀ }
end
omit h₀

-- Now we can apply the homotopy extension property of j'
lemma Ex_E : ∃ (E : I +> (I +> b) ⟶ x),
  E ∘ i ε @> (I +> b) = H₀.H ∧ E ∘ I &> j' = HH'' :=
hep_cof j' (relative_cylinder j hj) ε _ _ _ HH''iε

section E
parameters (E : I +> (I +> b) ⟶ x)
  (hE : E ∘ i ε @> (I +> b) = H₀.H ∧ E ∘ I &> j' = HH'')
-- Now E ∘ i ε.v is supposed to be a homotopy from f₁ to f₁' rel j.

include hE
lemma Eiεvi_ :
  E ∘ i ε.v @> (I +> b) ∘ i 0 @> b = f₁ ∧
  E ∘ i ε.v @> (I +> b) ∘ i 1 @> b = f₁' :=
have
  i.{u v} ε.v @> (I +> b) ∘ i 0 @> b = I &> j' ∘ I &> Po.map₀ ∘ i ε.v @> _ ∘ i₀ ∧
  i.{u v} ε.v @> (I +> b) ∘ i 1 @> b = I &> j' ∘ I &> Po.map₀ ∘ i ε.v @> _ ∘ i₁, begin
  split;
  { rw ←I.functoriality, unfold j', simp, erw i_nat_assoc,
    rw ←I.functoriality, unfold ii, simp,
    apply (i _).naturality }
end,
begin
  split;
  { rw ←associativity, rw this.1 <|> rw this.2,
    simp [hE.2, HH'', HH'],
    erw i_nat_assoc, dsimp, simp,
    -- dsimp: coprod vs (has_coproducts.coproduct _ _).ob?
    exact H.Hiεv <|> exact H'.Hiεv }
end

def Eiε : homotopy f₁ f₁' :=
{ H := E ∘ i ε.v @> (I +> b), Hi₀ := Eiεvi_.1, Hi₁ := Eiεvi_.2 }

local attribute [elab_simple] functor.Functor.onMorphisms
lemma Eiε_is_rel : Eiε.is_rel j :=
have i ε.v @> (I +> b) ∘ I &> j = I &> j' ∘ I &> Po.map₁ ∘ _, begin
  rw ←I.functoriality, unfold j', simp,
  rw ←(i ε.v).naturality, refl
end,
begin
  dsimp [homotopy.is_rel, Eiε] { iota := tt },
  rw [←associativity, this], simp [hE.2, HH'', GIp],
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

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
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
section
-- Homotopy equivalences as the weak equivalences of an I-category.
open homotopy_theory.cylinder
open homotopy_theory.weak_equivalences

parameters {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

parameters (C)
def homotopy_congruence ⦃a b : C⦄ := (homotopic : (a ⟶ b) → (a ⟶ b) → Prop)
instance : congruence homotopy_congruence :=
congruence.mk' (λ a b, homotopic_is_equivalence)
  (λ a b c f f' g, homotopic.congr_left g)
  (λ a b c f g g', homotopic.congr_right f)

instance homotopy_category.category_with_weak_equivalences :
  category_with_weak_equivalences (category_mod_congruence C homotopy_congruence) :=
isomorphisms_as_weak_equivalences

instance I_category.category_with_weak_equivalences : category_with_weak_equivalences C :=
preimage_with_weak_equivalences (quotient_functor C homotopy_congruence)

section
/-

Suppose f₀ : b → x is a map and G is a homotopy from u = f₀ ∘ j to
some other map u' : a → x. Using the homotopy extension property of j,
we obtain a homotopy f₀ ≃ f₁ extending G to a map f₁ with f₁ ∘ j = u'.
We show below that this construction is well-defined up to homotopy
rel j and defines a bijection between homotopy classes rel j of maps
extending u and homotopy classes rel j of maps extending u'.

This correspondence is not constructive in either direction since we
need to use the HEP, which is a mere existence statement. Therefore we
describe it as a relation and show that a homotopy class on either
side is related to a unique homotopy class on the other side.

We call this the "drag" relation induced by G, and imagine dragging
the restriction of f₀ to a along the homotopy G, with the rest of f₀
following along. A familiar example is the isomorphism πₙ(X, x) ≃
πₙ(X, y) induced by a path γ : x ↝ y in X.

-/

parameters {C}
parameters {a b : C} {j : a ⟶ b} (hj : is_cof j) {x : C}
include hj

section
variables (u : a ⟶ x)

def maps_extending : Type v := {v : b ⟶ x // v ∘ j = u}
instance maps_extending.homotopic_rel : setoid (maps_extending u) :=
{ r := λ f g, homotopic_rel j f.val g.val,
  -- TODO: preimage of an equivalence relation is an equivalence relation
  iseqv :=
    ⟨λ f, homotopic_rel.refl f.val,
     λ f g, homotopic_rel.symm hj,
     λ f g h, homotopic_rel.trans hj⟩ }

def homotopy_classes_extending_rel : Type v :=
quotient (maps_extending.homotopic_rel u)

end

section dir
-- Abstract over the direction of "dragging": f₀ to f₁ or f₁ to f₀.
parameters (u : endpoint → (a ⟶ x))
parameters (ε : endpoint) (G : homotopy_dir ε (u ε) (u ε.v))
include G

def drag_rel_dir : maps_extending (u ε) → maps_extending (u ε.v) → Prop :=
λ fε fεv, ∃ H : homotopy_dir ε fε.val fεv.val, H.H ∘ I &> j = G.H

lemma total (fε : maps_extending (u ε)) : ∃ fεv, drag_rel_dir fε fεv :=
let ⟨E, h₁, h₂⟩ := I_category.hep_cof j hj ε x fε.val G.H $
  by rw [fε.property, G.Hiε] in
⟨⟨E ∘ i ε.v @> b, by rw [i_nat_assoc, ←G.Hiεv, h₂]⟩,
 ⟨homotopy_dir.mk ε E h₁ rfl, by clear _let_match; cases ε; exact h₂⟩⟩

end dir

parameters (u u' : a ⟶ x)
parameters (G : homotopy u u')
include G

def drag_rel : maps_extending u → maps_extending u' → Prop :=
λ f₀ f₁, ∃ H : homotopy f₀.val f₁.val, H.H ∘ I &> j = G.H

local notation f₀ ` ~G `:50 f₁:50 := drag_rel f₀ f₁
local notation `[` b `,` x `]^` u:60 := homotopy_classes_extending_rel u

-- The relation ~G does not descend to the quotient: given a homotopy
-- f₀ ≃ f₀' rel u and a homotopy f₀ ≃ f₁ extending G, we may not be
-- able to find a homotopy f₀' ≃ f₁ extending G. Rather, two homotopy
-- classes are related when they have representatives which are
-- related by ~G.
def drag_rel_homotopy : [b, x]^u → [b, x]^u' → Prop :=
λ g₀ g₁, ∃ f₀ f₁, ⟦f₀⟧ = g₀ ∧ ⟦f₁⟧ = g₁ ∧ f₀ ~G f₁

private def uu' : endpoint → (a ⟶ x) := (λ ε, endpoint.cases_on ε u u')

lemma drag_rel_homotopy_total₀ (g₀) : ∃ g₁, drag_rel_homotopy g₀ g₁ :=
quotient.induction_on g₀ $ assume f₀,
  let ⟨f₁, h⟩ := total uu' 0 G f₀ in ⟨⟦f₁⟧, ⟨f₀, f₁, rfl, rfl, h⟩⟩

lemma drag_rel_homotopy_total₁ (g₁) : ∃ g₀, drag_rel_homotopy g₀ g₁ :=
quotient.induction_on g₁ $ assume f₁,
  let ⟨f₀, h⟩ := total uu' 1 G f₁ in ⟨⟦f₀⟧, ⟨f₀, f₁, rfl, rfl, h⟩⟩

lemma drag_rel_homotopy_unique₀ (g₀ g₁ g₁') :
  drag_rel_homotopy g₀ g₁ → drag_rel_homotopy g₀ g₁' → g₁ = g₁' :=
assume ⟨f₀, f₁, hf₀, hf₁, ⟨H, h⟩⟩ ⟨f₀', f₁', hf₀', hf₁', ⟨H', h'⟩⟩,
  have f₀.val ≃ f₀'.val rel j, from quotient.exact (hf₀.trans hf₀'.symm),
  let ⟨H₀, h₀⟩ := this in
  hf₁.symm.trans $
    (quotient.sound (equiv_private.f₁_f₂ j hj h₀ 0 h h') : ⟦f₁⟧ = ⟦f₁'⟧).trans hf₁'

lemma drag_rel_homotopy_unique₁ (g₀ g₀' g₁) :
  drag_rel_homotopy g₀ g₁ → drag_rel_homotopy g₀' g₁ → g₀ = g₀' :=
assume ⟨f₀, f₁, hf₀, hf₁, ⟨H, h⟩⟩ ⟨f₀', f₁', hf₀', hf₁', ⟨H', h'⟩⟩,
  have f₁.val ≃ f₁'.val rel j, from quotient.exact (hf₁.trans hf₁'.symm),
  let ⟨H₁, h₁⟩ := this in
  hf₀.symm.trans $
    (quotient.sound (equiv_private.f₁_f₂ j hj h₁ 1 h h') : ⟦f₀⟧ = ⟦f₀'⟧).trans hf₀'

end

end
end homotopy_theory.cofibrations
