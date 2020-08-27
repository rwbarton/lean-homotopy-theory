import category_theory.colimits
import category_theory.colimit_lemmas

import .category

/-

Construction of the basic finite colimits in Top.

-/

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}


section initial_object

protected def empty : Top := Top.mk_ob pempty
protected def empty_induced (Z : Top) : Top.empty ⟶ Z :=
Top.mk_hom (λ x, pempty.cases_on (λ _, Z) x) (by continuity)
protected def empty_is_initial_object : Is_initial_object.{u u+1} Top.empty :=
Is_initial_object.mk' Top.empty_induced (assume Z k k', by ext x; cases x)

instance : has_initial_object.{u} Top :=
⟨⟨Top.empty, Top.empty_is_initial_object⟩⟩

protected def is_initial_object_of_to_empty (A : Top) (h : A → pempty) :
  Is_initial_object.{u} A :=
have continuous h, begin
  intros u hu,
  have : u = ∅, from set.eq_empty_iff_forall_not_mem.mpr (pempty.rec _),
  rw [this, set.preimage_empty],
  exact is_open_empty
end,
have h' : A ⟶ Top.empty := Top.mk_hom h this,
Is_initial_object.mk'
  (λ Z, Top.empty_induced Z ∘ h')
  (assume Z k k', begin ext x, cases h x end)

end initial_object


section coproduct

section construction
parameters (X₀ X₁ : Top)

protected def coproduct_object : Top := Top.mk_ob (X₀ ⊕ X₁)
protected def coproduct_map₀ : X₀ ⟶ coproduct_object := Top.mk_hom sum.inl
protected def coproduct_map₁ : X₁ ⟶ coproduct_object := Top.mk_hom sum.inr

variables ⦃Z : Top⦄ (h₀ : X₀ ⟶ Z) (h₁ : X₁ ⟶ Z)
protected def coproduct_induced : coproduct_object ⟶ Z :=
Top.mk_hom (λ x, sum.cases_on x h₀ h₁) (by continuity!)

protected def coproduct_induced_commutes₀ : coproduct_induced h₀ h₁ ∘ coproduct_map₀ = h₀ :=
by ext; refl

protected def coproduct_induced_commutes₁ : coproduct_induced h₀ h₁ ∘ coproduct_map₁ = h₁ :=
by ext; refl

protected def coproduct_uniqueness {k k' : coproduct_object ⟶ Z}
  (e₀ : k ∘ coproduct_map₀ = k' ∘ coproduct_map₀)
  (e₁ : k ∘ coproduct_map₁ = k' ∘ coproduct_map₁) : k = k' :=
begin
  ext x,
  cases x,
  { exact @@Top.hom_congr e₀ x },
  { exact @@Top.hom_congr e₁ x }
end

protected def coproduct_is_coproduct : Is_coproduct coproduct_map₀ coproduct_map₁ :=
Is_coproduct.mk' coproduct_induced
  coproduct_induced_commutes₀ coproduct_induced_commutes₁
  coproduct_uniqueness

end construction

instance Top.has_coproducts : has_coproducts.{u} Top :=
⟨λ X₀ X₁,
  { ob := Top.coproduct_object X₀ X₁,
    map₀ := Top.coproduct_map₀ X₀ X₁,
    map₁ := Top.coproduct_map₁ X₀ X₁,
    is_coproduct := Top.coproduct_is_coproduct X₀ X₁ }⟩

end coproduct


section coequalizer

section construction
parameters {X Y : Top} (f₀ f₁ : X ⟶ Y)

protected def coeq_rel : Y → Y → Prop :=
λ y₀ y₁, ∃ x, y₀ = f₀ x ∧ y₁ = f₁ x

protected def coequalizer_object : Top :=
Top.mk_ob (quot coeq_rel)

protected def coequalizer_map : Y ⟶ Top.coequalizer_object f₀ f₁ :=
Top.mk_hom (quot.mk coeq_rel)

protected lemma coequalizer_commutes : coequalizer_map ∘ f₀ = coequalizer_map ∘ f₁ :=
by ext x; exact quot.sound ⟨x, rfl, rfl⟩

variable ⦃Z : Top⦄

protected def coequalizer_induced {k : Y ⟶ Z} (e : k ∘ f₀ = k ∘ f₁) :
  coequalizer_object ⟶ Z :=
Top.mk_hom
  (@quot.lift _ coeq_rel _ k
    (assume y₀ y₁ ⟨x, h₀, h₁⟩, by rw [h₀, h₁]; exact Top.hom_congr e x))
  (by continuity)

-- TODO: How can we avoid duplicating the proof on the last line here?
protected lemma coequalizer_induced_commutes {k : Y ⟶ Z} (e : k ∘ f₀ = k ∘ f₁) :
  coequalizer_induced e ∘ coequalizer_map = k :=
Top.hom_eq $ assume x,
  @quot.lift_beta _ coeq_rel _ k
    (assume y₀ y₁ ⟨x, h₀, h₁⟩, by rw [h₀, h₁]; exact Top.hom_congr e x) _

protected lemma coequalizer_uniqueness {k k' : coequalizer_object ⟶ Z}
  (e : k ∘ coequalizer_map = k' ∘ coequalizer_map) : k = k' :=
Top.hom_eq $ λ x, quot.ind (Top.hom_congr e) x

protected def coequalizer_is_coequalizer : Is_coequalizer f₀ f₁ coequalizer_map :=
Is_coequalizer.mk' coequalizer_commutes coequalizer_induced
  coequalizer_induced_commutes coequalizer_uniqueness

end construction

instance Top.has_coequalizers : has_coequalizers.{u} Top :=
⟨λ X Y f₀ f₁,
  { ob := Top.coequalizer_object f₀ f₁,
    map := Top.coequalizer_map f₀ f₁,
    is_coequalizer := Top.coequalizer_is_coequalizer _ _ }⟩

end coequalizer


section pushout

instance : has_pushouts.{u} Top :=
has_pushouts_of_has_coequalizers_and_coproducts

end pushout


end «Top»
end homotopy_theory.topological_spaces
