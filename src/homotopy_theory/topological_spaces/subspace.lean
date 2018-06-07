import .category

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
namespace Top

local notation `Top` := Top.{u}

def incl {X : Top} (A : set X) : Top.mk_ob A ⟶ X :=
Top.mk_hom subtype.val

def embedding_incl {X : Top} (A : set X) : embedding (incl A) :=
embedding_subtype_val

def factor_through_incl {W X : Top} (f : W ⟶ X) (A : set X) (h : set.range f ⊆ A) :
  W ⟶ Top.mk_ob A :=
Top.mk_hom (λ (w : W), ⟨f w, h (set.mem_range_self w)⟩) (by continuity)

@[simp] lemma factor_through_incl_commutes {W X : Top} (f : W ⟶ X) (A : set X) (h : set.range f ⊆ A) :
  incl A ∘ factor_through_incl f A h = f :=
by ext; refl

end «Top»
end homotopy_theory.topological_spaces
