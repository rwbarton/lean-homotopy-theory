import tactic.slice
import category_theory.colimit_lemmas
import category_theory.pushout_fold
import homotopy_theory.formal.cofibrations.cofibration_category
import homotopy_theory.formal.cofibrations.cylinder
import homotopy_theory.formal.cofibrations.factorization_from_cylinder
import homotopy_theory.formal.cofibrations.homotopy
import homotopy_theory.formal.cofibrations.left_proper
import .cylinder_object
import .dold

universes v u

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open homotopy_theory.cylinder (renaming homotopic_rel → homotopic_rel_cylinder)
open homotopy_theory.weak_equivalences
open precofibration_category

-- An I-category gives rise to a cofibration category with the same
-- cofibrations in which the weak equivalences are the homotopy
-- equivalences.

variables {C : Type u} [category.{v} C]
  [has_initial_object.{v} C] [has_coproducts.{v} C] [I_category.{v} C]

-- Every object is fibrant.
lemma all_objects_fibrant (x : C) : fibrant x :=
assume y j ⟨jc, jw⟩,
let ⟨⟨r, h, H⟩⟩ := (heq_iff_sdr_inclusion jc).mp jw in ⟨r, h⟩

instance I_category.cofibration_category : cofibration_category.{v} C :=
cofibration_category.mk_from_cylinder
  (assume a b a' b' f g f' g' po ⟨fc, fw⟩,
    ⟨precofibration_category.pushout_is_cof po fc, pushout_is_acof po fc fw⟩)
  (assume a, ⟨I.obj a, ii @> a, p @> a, cof_ii a, heq_p, pii⟩)
  (assume x, ⟨x, 𝟙 x, ⟨cof_id x, weq_id x⟩, all_objects_fibrant x⟩)

-- The functor I produces cylinder objects in the general sense of
-- cofibration categories.
def canonical_cylinder (b : C) :
  relative_cylinder (all_objects_cofibrant.cofibrant.{v} b) :=
⟨I.obj b,
 (pushout_by_cof (!b) (!b) _).is_pushout.induced (i 0 @> b) (i 1 @> b)
   (category_theory.initial.uniqueness _ _),
 p @> b,
 -- We proved ii : b ⊔ b → Ib is a cofibration; need to massage this
 -- into a map from the pushout over the initial object.
 let po := pushout_by_cof (!b) (!b) (all_objects_cofibrant.cofibrant.{v} b),
     -- The map we need to show is a cofibration
     ii' := po.is_pushout.induced (i 0 @> b) (i 1 @> b)
       (category_theory.initial.uniqueness _ _),
     c : Is_coproduct po.map₀ po.map₁ :=
       Is_coproduct_of_Is_pushout_of_Is_initial po.is_pushout
         has_initial_object.initial_object.is_initial_object,
     j : iso (b ⊔ b) po.ob := isomorphic_coprod_of_Is_coproduct c in
 have ii' ∘ j.hom = ii @> b, begin
   dsimp [j, isomorphic_coprod_of_Is_coproduct];
   apply coprod.uniqueness; rw ←assoc; simp [ii]
 end,
 have ii' = ii @> b ∘ j.inv, by rw ←this; simp,
 show is_cof ii',
 by rw this; exact cof_comp (cof_iso j.symm) (cof_ii b),
 heq_p,
 begin
   apply (pushout_by_cof (!b) (!b) _).is_pushout.uniqueness;
   { rw ←assoc, simp }
 end⟩

/-
         I a → a
          ↓ po ↓
 b ⊔ b → I b → c → b
   a
-/
def canonical_relative_cylinder {a b : C} {j : a ⟶ b} (hj : is_cof j) :
  relative_cylinder hj :=
let po := pushout_by_cof (I.map j) (p.app a) (I_preserves_cofibrations hj) in
⟨po.ob,
 (pushout_by_cof j j _).is_pushout.induced ((i 0).app b ≫ po.map₀) ((i 1).app b ≫ po.map₀)
   begin
     erw [←assoc, ←assoc, (i 0).naturality, (i 1).naturality],
     rw [assoc, assoc, po.is_pushout.commutes, ←assoc, ←assoc],
     simp
   end,
 po.is_pushout.induced (p.app b) j (p.naturality j),

/-
 a ⊔ a → I a →   a
   ↓  po₁ ↓ po₂  ↓
 b ⊔ b →  ⬝  → b ⊔ b
                 a
          ↓ po₃  ↓
         I b →   c → b
-/
 begin
   let po₀ := pushout_by_cof j j hj,
   let abb : a ⟶ po₀.ob := po₀.map₀ ∘ j,
   let po₁ := pushout_by_cof _ (ii.app a) (cof_coprod hj hj),
   let l := po₁.is_pushout.induced (coprod.induced po₀.map₀ po₀.map₁) (abb ∘ p.app a)
   begin
     apply coprod.uniqueness,
       { rw [←assoc, coprod_of_maps_commutes₀, assoc, coprod.induced_commutes₀],
         rw [iii₀_assoc, ←assoc, pi_components, id_comp] },
       { rw [←assoc, coprod_of_maps_commutes₁, assoc, coprod.induced_commutes₁],
         rw [iii₁_assoc, ←assoc, pi_components, id_comp, ←po₀.is_pushout.commutes] }
   end,
   have po₁₂ : Is_pushout (coprod_of_maps j j) (coprod.fold a) _ _ :=
     Is_pushout_fold po₀.is_pushout,
   have po₂ : Is_pushout po₁.map₁ (p.app a) l abb,
   { refine Is_pushout_of_Is_pushout_of_Is_pushout' po₁.is_pushout _ _,
     { convert po₁₂,
       { apply pii },
       { simp } },
     { simp } },
   have po₂₃ : Is_pushout (I.map j) (p.app a) _ _ := po.is_pushout,
   let m := _,                  -- naming part of the type of a hypothesis
   have : is_cof m := I_category.relative_cylinder j hj,
   let n := _,                  -- naming part of the type of the goal
   change is_cof n,
   have po₃ : Is_pushout m l po.map₀ n,
   { refine Is_pushout_of_Is_pushout_of_Is_pushout_vert' po₂ _ _,
     convert po₂₃,
     { simp, refl },
     { have : po.map₀ ∘ (i 0).app b ∘ j = po.map₁,
       { rw ←assoc,
         erw (i 0).naturality,
         rw [assoc, po.is_pushout.commutes, ←assoc, pi_components, id_comp] },
       simpa using this },
     { apply po₁.is_pushout.uniqueness; rw [←assoc, ←assoc],
       { simp only [Is_pushout.induced_commutes₀, Is_pushout.induced_commutes₁],
         apply coprod.uniqueness; rw [←assoc, ←assoc]; simp },
       { simp only [assoc, Is_pushout.induced_commutes₀, Is_pushout.induced_commutes₁],
         slice_rhs 2 3 { change (i 0).app b ∘ ((functor.id _).map j), rw (i 0).naturality },
         simp only [assoc],
         erw [po.is_pushout.commutes],
         slice_rhs 2 3 { rw pi_components },
         dsimp, simp } } },
   exact pushout_is_cof po₃ this
 end,
 begin
   have : is_weq po.map₀ :=
     left_proper.pushout_weq_by_cof po.is_pushout (I_preserves_cofibrations hj) heq_p,
   refine category_with_weak_equivalences.weq_of_comp_weq_left this _,
   simpa using heq_p,
 end,
 begin
   symmetry,
   apply pushout_induced_eq_iff; rw ←assoc; simp
 end⟩

section homotopy
variables {a b x : C} {j : a ⟶ b} (hj : is_cof j) (f₀ f₁ : b ⟶ x)

lemma homotopic_rel_iff_cylinder :
  homotopic_rel hj f₀ f₁ ↔ homotopic_rel_cylinder j f₀ f₁ :=
let po := pushout_by_cof (I.map j) (p.app a) (I_preserves_cofibrations hj) in
begin
  split; intro H,
  { rcases homotopic_rel' (canonical_relative_cylinder hj) (all_objects_fibrant x) f₀ f₁ H
      with ⟨H, Hi₀, Hi₁⟩,
    dsimp [canonical_relative_cylinder, relative_cylinder.i₀, relative_cylinder.i₁] at Hi₀ Hi₁,
    simp at Hi₀ Hi₁,
    refine ⟨⟨po.map₀ ≫ H, _, _⟩, _⟩,
    { rw [←Hi₀, ←assoc, ←assoc], refl },
    { rw [←Hi₁, ←assoc, ←assoc], refl },
    { dsimp [homotopy.is_rel],
      rw [←Hi₀],
      slice_rhs 2 3 { change (functor.id _).map j ≫ (i 0).app b, rw (i 0).naturality },
      slice_lhs 1 2 { rw po.is_pushout.commutes },
      slice_rhs 3 4 { change I.map j ≫ po.map₀, rw po.is_pushout.commutes },
      slice_rhs 2 3 { rw pi_components },
      simp } },
  { rcases H with ⟨⟨H, Hi₀, Hi₁⟩, r⟩,
    refine ⟨canonical_relative_cylinder hj, ⟨⟨_, _, _⟩⟩⟩,
    refine po.is_pushout.induced H (j ≫ f₀) r,
    { convert Hi₀ using 1,
      dsimp [relative_cylinder.i₀, canonical_relative_cylinder], simp },
    { convert Hi₁ using 1,
      dsimp [relative_cylinder.i₁, canonical_relative_cylinder], simp } }
end

end homotopy

end homotopy_theory.cofibrations
