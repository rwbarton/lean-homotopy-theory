import homotopy_theory.formal.cylinder.homotopy
import .definitions
import .homotopy_lemmas
import .homotopy_equivalences

/-

Dold's theorem: Suppose j : A → X and j' : A → X' are cofibrations and
f : X → X' is a homotopy equivalence with f ∘ j = j'. Then f is a
homotopy equivalence under A.

-/

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
section C
open categories.has_initial_object
open homotopy_theory.cylinder
open I_category

parameters {C : Type u} [category.{u v} C] [has_initial_object.{u v} C]
  [has_coproducts.{u v} C] [Icat : I_category.{u v} C]
include Icat

-- [Kamps & Porter, Lemma I.6.4]. Apparently, we already did most of
-- the hard work.
lemma dold_lemma {a x : C} {j : a ⟶ x} (hj : is_cof j) {g : x ⟶ x} (hg : g ∘ j = j)
  (h : g ≃ 𝟙 x) : ∃ g', g' ∘ j = j ∧ g' ∘ g ≃ 𝟙 x rel j :=
let ⟨φ⟩ := h,
    φ' := φ.congr_right j,
    ⟨ψ, hψ₁, hψ₂⟩ := hep_cof j hj 0 x (𝟙 x) φ'.H (by rw [φ'.Hi₀, hg]; simp),
    g' := ψ ∘ i 1 @> x,
    ψh : homotopy (𝟙 x) g' := { H := ψ, Hi₀ := hψ₁, Hi₁ := rfl } in
have g' ∘ j = j, by dsimp [g']; rw [i_nat_assoc, hψ₂, φ'.Hi₁]; simp,
suffices H : g' ∘ g ≃ 𝟙 x rel j, from ⟨g', this, H⟩,
let ψhg : homotopy g (g' ∘ g) :=
  @eq.rec_on (x ⟶ x) (𝟙 x ∘ g) (λ f, homotopy f (g' ∘ g)) g (by simp)
    (ψh.congr_right g) in
have ψhg.H ∘ I &> j = φ'.H, begin
  convert hψ₂ using 1, rw homotopy.eq_rec_on_left,
  change ψ ∘ I &> g ∘ I &> j = ψ ∘ I &> j,
  rw [←associativity, ←I.functoriality, hg]
end,
equiv_private.f₁_f₂ j hj homotopy.refl_is_rel 0 this rfl

lemma dold_lemma' {a x x' : C} {j : a ⟶ x} (hj : is_cof j) (f : x ⟶ x') (r : x' ⟶ x)
  (hr : r ∘ f ∘ j = j) (h : r ∘ f ≃ 𝟙 x) : ∃ r', r' ∘ f ∘ j = j ∧ r' ∘ f ≃ 𝟙 x rel j :=
let ⟨g', hg'₁, hg'₂⟩ := dold_lemma hj hr h in
⟨g' ∘ r,
 calc
  g' ∘ r ∘ f ∘ j = g' ∘ (r ∘ f ∘ j) : by simp
  ...            = j                : by rw [hr, hg'₁],
 by convert hg'₂ using 1; simp⟩

-- Ugh! We'd like to use `calc` to compose homotopies rel j', but
-- homotopic_rel.trans has an extra `is_cof j` argument which we have
-- no way to provide explicitly. So, we locally arrange for the
-- argument to be provided by the type class system.
local attribute [class] is_cof

@[trans] private lemma homotopic_rel.trans' {a b x : C} {j : a ⟶ b} [hj : is_cof j]
  {f₀ f₁ f₂ : b ⟶ x} (h₁ : f₀ ≃ f₁ rel j) (h₂ : f₁ ≃ f₂ rel j) : f₀ ≃ f₂ rel j :=
homotopic_rel.trans hj h₁ h₂

-- Why is this necessary? doesn't work without `local`
local notation f₀ ` ≃ `:50 f₁:50 := homotopic f₀ f₁

-- [Kamps & Porter, Lemma I.6.3]
lemma dold_theorem {a x x' : C} {j : a ⟶ x} (hj : is_cof j) {j' : a ⟶ x'} (hj' : is_cof j')
  {f : x ⟶ x'} (hf : f ∘ j = j') (hef : homotopy_equivalence f) :
  ∃ h : x' ⟶ x, h ∘ j' = j ∧ h ∘ f ≃ 𝟙 _ rel j ∧ f ∘ h ≃ 𝟙 _ rel j' :=
let ⟨f', hf'₁, hf'₂⟩ := homotopy_equivalence_iff.mp hef in
have f' ∘ j' ≃ j, from calc
  f' ∘ j' = f' ∘ f ∘ j : by rw ←hf; simp
  ...     ≃ j          : by convert hf'₁.congr_right j; simp,
let ⟨H⟩ := this,
    ⟨H', hH'₁, hH'₂⟩ := hep_cof j' hj' 0 x f' H.H H.Hi₀.symm,
    f'' := H' ∘ i 1 @> x' in
have f' ≃ f'', from ⟨⟨H', hH'₁, rfl⟩⟩,
have f'' ∘ j' = j, by dsimp [f'']; rw [i_nat_assoc, hH'₂, H.Hi₁],
let ⟨h, hh₁, hh₂⟩ :=
      dold_lemma' hj f f'' (by rw [←associativity, hf, this]) $ calc
        f'' ∘ f ≃ f' ∘ f : ‹f' ≃ f''›.symm.congr_right f
        ...     ≃ 𝟙 x    : hf'₁ in
have f ∘ h ≃ 𝟙 x', from calc
  f ∘ h ≃ f ∘ h ∘ (f ∘ f')  : by convert hf'₂.symm.congr_left (f ∘ h) using 1; simp
  ...   ≃ f ∘ h ∘ (f ∘ f'') : (‹f' ≃ f''›.congr_left f).congr_left (f ∘ h)
  ...   = f ∘ (h ∘ f) ∘ f'' : by simp
  ...   ≃ f ∘ 𝟙 x ∘ f''     : (hh₂.forget_rel.congr_left f).congr_right f''
  ...   ≃ f ∘ f'            : by convert ‹f' ≃ f''›.symm.congr_left f; simp
  ...   ≃ 𝟙 x'              : hf'₂,
have fhj' : f ∘ h ∘ j' = j', by rw [←hf, ←associativity]; congr; simp [hh₁],
let ⟨k, hk₁, hk₂⟩ := dold_lemma' hj' h f fhj' this in
have hk₂' : k ∘ h ≃ 𝟙 x' rel f ∘ h ∘ j', by convert hk₂; exact fhj',
have hh₂' : h ∘ f ≃ 𝟙 x rel h ∘ j', by convert hh₂; rw [←hf]; simp [hh₁],
⟨h, by rw [←hf]; simp [hh₁], hh₂, calc
  f ∘ h ≃ (k ∘ h) ∘ (f ∘ h) rel j'  : by convert (hk₂'.congr_right (f ∘ h)).symm hj' using 1; simp
  ...   = k ∘ (h ∘ f) ∘ h           : by simp
  ...   ≃ k ∘ (𝟙 x) ∘ h     rel j'  : by convert (hh₂'.congr_left k).congr_right h using 1; refl
  ...   = k ∘ h                     : by simp
  ...   ≃ 𝟙 x'              rel j'  : hk₂⟩

end C
end homotopy_theory.cofibrations
