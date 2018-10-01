import category_theory.category
import category_theory.colimits
import category_theory.colimit_lemmas
import category_theory.types

import .homeomorphism
import .subspace

open set

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces

namespace Set
local notation `Set` := Type u

def mk_ob (α : Set) : Set := α

def incl' {α : Set} (A B : set α) (h : A ⊆ B) : mk_ob A ⟶ mk_ob B :=
λ p, ⟨p.val, h p.property⟩

section inter_union
variables {X : Set} {A₀ A₁ : set X}

local notation `A₀₁` := A₀ ∩ A₁
local notation `A` := (A₀ ∪ A₁ : set X)

local notation `i₀` := incl' A₀₁ A₀ (set.inter_subset_left A₀ A₁)
local notation `i₁` := incl' A₀₁ A₁ (set.inter_subset_right A₀ A₁)
local notation `j₀` := incl' A₀ A (set.subset_union_left A₀ A₁)
local notation `j₁` := incl' A₁ A (set.subset_union_right A₀ A₁)

section glue
variables ⦃β : Set⦄ (h₀ : mk_ob A₀ ⟶ β) (h₁ : mk_ob A₁ ⟶ β)
variable (e : h₀ ∘ i₀ = h₁ ∘ i₁)
include e

local attribute [instance] classical.prop_decidable

noncomputable def glue : mk_ob A ⟶ β :=
λ a, if h : a.val ∈ A₀ then h₀ ⟨a.val, h⟩ else h₁ ⟨a.val, a.property.resolve_left h⟩

lemma glue_commutes₀ : glue h₀ h₁ e ∘ j₀ = h₀ :=
by funext a; have := a.property; simp [glue, incl', this]

lemma glue_commutes₁ : glue h₀ h₁ e ∘ j₁ = h₁ :=
begin
  funext a, change (if h : _ then _ else _) = h₁ a, cases a with v p,
  split_ifs, { exact congr_fun e ⟨v, h, p⟩ }, { refl }
end

end glue

lemma uniqueness ⦃β : Set⦄ (k k' : mk_ob A ⟶ β)
  (e₀ : k ∘ j₀ = k' ∘ j₀) (e₁ : k ∘ j₁ = k' ∘ j₁) : k = k' :=
begin
  funext a, rcases a with ⟨v, p₀|p₁⟩,
  { exact @@congr_fun _ _ _ e₀ ⟨v, p₀⟩ },
  { exact @@congr_fun _ _ _ e₁ ⟨v, p₁⟩ }
end

variables (A₀ A₁)
include A₀ A₁
noncomputable def Is_pushout_inter_union : Is_pushout i₀ i₁ j₀ j₁ :=
Is_pushout.mk' rfl glue glue_commutes₀ glue_commutes₁ uniqueness

end inter_union

end «Set»


namespace Top
local notation `Top` := Top.{u}

section inter_union
variables {X : Top} {A₀ A₁ : set X} (ha₀ : is_closed A₀) (ha₁ : is_closed A₁)
-- Other assumptions are possible, e.g., A₀, A₁ both open.

local notation `A₀₁` := A₀ ∩ A₁
local notation `A` := (A₀ ∪ A₁ : set X)

local notation `i₀` := incl' A₀₁ A₀ (set.inter_subset_left A₀ A₁)
local notation `i₁` := incl' A₀₁ A₁ (set.inter_subset_right A₀ A₁)
local notation `j₀` := incl' A₀ A (set.subset_union_left A₀ A₁)
local notation `j₁` := incl' A₁ A (set.subset_union_right A₀ A₁)
local notation `i'₀` := Set.incl' A₀₁ A₀ (set.inter_subset_left A₀ A₁)
local notation `i'₁` := Set.incl' A₀₁ A₁ (set.inter_subset_right A₀ A₁)
local notation `j'₀` := Set.incl' A₀ A (set.subset_union_left A₀ A₁)
local notation `j'₁` := Set.incl' A₁ A (set.subset_union_right A₀ A₁)

local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

instance Set.mk_ob.topological_space (α : Type*) [t : topological_space α] :
  topological_space (Set.mk_ob α) := t

lemma continuous_iff {Z : Top} (k : A → Z) :
  continuous k ↔ continuous (k ∘ j'₀) ∧ continuous (k ∘ j'₁) :=
iff.intro (assume h, ⟨by continuity, by continuity⟩)
  (assume ⟨h₀, h₁⟩,
    let c : bool → set A := λ i, bool.rec_on i {a | a.val ∈ A₀} {a | a.val ∈ A₁} in
    have h_lf : locally_finite c :=
      locally_finite_of_finite ⟨fintype.of_equiv _ (equiv.set.univ bool).symm⟩,
    have h_is_closed : ∀ i, is_closed (c i) :=
      assume i, bool.rec_on i
        (continuous_iff_is_closed.mp continuous_subtype_val _ ha₀)
        (continuous_iff_is_closed.mp continuous_subtype_val _ ha₁),
    have h_cover : ∀ a, ∃ i, a ∈ c i :=
      assume a, a.property.elim (λ h, ⟨ff, h⟩) (λ h, ⟨tt, h⟩),
    have f_cont : ∀ i, continuous (λ (x : subtype (c i)), k x.val) :=
      assume i, bool.rec_on i
        (have continuous (function.comp (k ∘ j'₀) (λ (x : subtype (c ff)), ⟨x.val.val, x.property⟩)),
          by continuity, begin convert this, funext x, rcases x with ⟨⟨_, _⟩, _⟩, refl end)
        (have continuous (function.comp (k ∘ j'₁) (λ (x : subtype (c tt)), ⟨x.val.val, x.property⟩)),
          by continuity, begin convert this, funext x, rcases x with ⟨⟨_, _⟩, _⟩, refl end),
    continuous_subtype_is_closed_cover c h_lf h_is_closed h_cover f_cont)

variables (A₀ A₁)
include A₀ A₁
noncomputable def Is_pushout_inter_union : Is_pushout i₀ i₁ j₀ j₁ :=
Is_pushout.mk $ λ Z, calc
  univ ~~ {k : {k : A → Z // continuous (k ∘ j'₀) ∧ continuous (k ∘ j'₁)} | true}
       : Bij_on.congr_subtype (ext (continuous_iff ha₀ ha₁))
   ... ~~ {p : {p : (A₀ → Z) × (A₁ → Z) // continuous p.1 ∧ continuous p.2} | p.val.1 ∘ i'₀ = p.val.2 ∘ i'₁}
       : ((Set.Is_pushout_inter_union A₀ A₁).universal Z).restrict_to_subtype (λ p, continuous p.1 ∧ continuous p.2)
   ... ~~ {p : (Top.mk_ob A₀ ⟶ Z) × (Top.mk_ob A₁ ⟶ Z) | p.1 ∘ i₀ = p.2 ∘ i₁}
       : by convert Bij_on.restrict_equiv equiv.subtype_prod_subtype_equiv_subtype.symm _;
            ext; simp only [Top.hom_eq2]; refl

local notation `k₀` := incl A₀
local notation `k₁` := incl A₁
variables (h : A₀ ∪ A₁ = univ)

include h
def union_is_X : homeomorphism (Top.mk_ob A) X :=
{ hom := incl _,
  inv := Top.mk_hom (λ x, ⟨x, by rw h; exact trivial⟩) (by continuity),
  hom_inv_id' := by ext p; cases p; refl,
  inv_hom_id' := by ext p; refl }

noncomputable def Is_pushout_inter_of_cover : Is_pushout i₀ i₁ k₀ k₁ :=
Is_pushout_of_isomorphic'
  (Is_pushout_inter_union A₀ A₁ ha₀ ha₁) (union_is_X A₀ A₁ h)

end inter_union

end «Top»

end homotopy_theory.topological_spaces
