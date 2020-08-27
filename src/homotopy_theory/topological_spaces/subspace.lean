import .category
import for_mathlib.data_set_basic

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}

def incl {X : Top} (A : set X) : Top.mk_ob A ⟶ X :=
Top.mk_hom subtype.val

def embedding_incl {X : Top} (A : set X) : embedding (incl A) :=
embedding_subtype_coe

noncomputable def factor_through_embedding {W X Y : Top} {f : W ⟶ Y} {g : X ⟶ Y}
  (hf : set.range f ⊆ set.range g) (hg : embedding g) : W ⟶ X :=
Top.mk_hom (classical.some $ (factors_iff f g).mpr hf) $
  by rw [hg.continuous_iff, ←classical.some_spec ((factors_iff f g).mpr hf)]; exact f.2

@[simp] lemma factor_through_embedding_commutes {W X Y : Top} {f : W ⟶ Y} {g : X ⟶ Y}
  {hf : set.range f ⊆ set.range g} {hg : embedding g} : factor_through_embedding hf hg ≫ g = f :=
Top.hom_eq2.mpr $
(classical.some_spec ((factors_iff f g).mpr hf)).symm

def factor_through_incl {W X : Top} (f : W ⟶ X) (A : set X) (h : set.range f ⊆ A) :
  W ⟶ Top.mk_ob A :=
Top.mk_hom (λ (w : W), ⟨f w, h (set.mem_range_self w)⟩) (by continuity)

@[simp] lemma factor_through_incl_commutes {W X : Top} (f : W ⟶ X) (A : set X) (h : set.range f ⊆ A) :
  incl A ∘ factor_through_incl f A h = f :=
by ext; refl

lemma embedding_of_embedding_comp {X Y Z : Top} {f : X ⟶ Y} (g : Y ⟶ Z)
  (hgf : embedding (g ∘ f)) : embedding f :=
embedding_of_embedding_compose f.2 g.2 hgf

def incl' {X : Top} (A B : set X) (h : A ⊆ B) : Top.mk_ob A ⟶ Top.mk_ob B :=
Top.mk_hom (λ a, ⟨a.val, h a.property⟩) (by continuity!)

end «Top»
end homotopy_theory.topological_spaces
