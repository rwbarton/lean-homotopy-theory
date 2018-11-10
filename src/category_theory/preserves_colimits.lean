import category_theory.base
import category_theory.colimits
import category_theory.adjunctions
import data.bij_on

open set

universes u₁ v₁ u₂ v₂

namespace category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

variables {C : Type u₁} [catC : category.{u₁ v₁} C]
variables {D : Type u₂} [catD : category.{u₂ v₂} D]
include catC catD

class preserves_initial_object (F : C ↝ D) :=
(Is_initial_object_of_Is_initial_object :
  Π {a : C}, Is_initial_object.{u₁ v₁} a → Is_initial_object.{u₂ v₂} (F.obj a))

class preserves_coproducts (F : C ↝ D) :=
(Is_coproduct_of_Is_coproduct :
  Π {a₀ a₁ b : C} {f₀ : a₀ ⟶ b} {f₁ : a₁ ⟶ b},
  Is_coproduct f₀ f₁ → Is_coproduct (F &> f₀) (F &> f₁))

class preserves_pushouts (F : C ↝ D) :=
(Is_pushout_of_Is_pushout :
  Π {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c},
  Is_pushout f₀ f₁ g₀ g₁ → Is_pushout (F &> f₀) (F &> f₁) (F &> g₀) (F &> g₁))

section left_adjoint

variables {F : C ↝ D} {G : D ↝ C} (adj : adjunction F G)

def left_adjoint_preserves_initial_object : preserves_initial_object F :=
⟨λ a ai, Is_initial_object.mk $ λ x,
  Is_equiv.mk ((adj.hom_equivalence a x).trans (ai.universal (G.obj x)).e)
    (by ext; refl)⟩

-- TODO: show left adjoints preserve coproducts

local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

def left_adjoint_preserves_pushout : preserves_pushouts F :=
⟨λ a b₀ b₁ c f₀ f₁ g₀ g₁ po, Is_pushout.mk $ λ x,
  have _ := calc
    (univ : set (F.obj c ⟶ x))
      ~~ (univ : set (c ⟶ G.obj x))
      : Bij_on.of_equiv (adj.hom_equivalence c x)
  ... ~~ {p : (b₀ ⟶ G.obj x) × (b₁ ⟶ G.obj x) | p.1 ∘ f₀ = p.2 ∘ f₁}
      : po.universal (G.obj x)
  ... ~~ {p : (b₀ ⟶ G.obj x) × (b₁ ⟶ G.obj x) | _}
      :
  begin
    convert Bij_on.refl _, funext p, cases p with p1 p2,
    change
      ((adj.hom_equivalence b₀ x).symm p1 ∘ F &> f₀ =
       (adj.hom_equivalence b₁ x).symm p2 ∘ F &> f₁) =
      (p1 ∘ f₀ = p2 ∘ f₁),
    transitivity
      ((adj.hom_equivalence a x).symm (p1 ∘ f₀) =
       (adj.hom_equivalence a x).symm (p2 ∘ f₁)),
    { rw adjunction.hom_equivalence_symm_naturality,
      rw adjunction.hom_equivalence_symm_naturality },
    { simp }
  end
  ... ~~ {p : (F.obj b₀ ⟶ x) × (F.obj b₁ ⟶ x) | p.1 ∘ (F &> f₀) = p.2 ∘ (F &> f₁)}
      : Bij_on.restrict''
          (Bij_on.prod'
            (Bij_on.of_equiv (adj.hom_equivalence b₀ x).symm)
            (Bij_on.of_equiv (adj.hom_equivalence b₁ x).symm))
          (λ p, p.1 ∘ (F &> f₀) = p.2 ∘ (F &> f₁)),
  begin
    convert this,
    funext k,
    change (k ∘ F &> g₀, k ∘ F &> g₁) =
      ((adj.hom_equivalence b₀ x).symm (adj.hom_equivalence c x k ∘ g₀),
       (adj.hom_equivalence b₁ x).symm (adj.hom_equivalence c x k ∘ g₁)),
    rw adj.hom_equivalence_symm_naturality,
    rw adj.hom_equivalence_symm_naturality,
    simp
  end⟩

end left_adjoint

instance has_right_adjoint.preserves_initial_object (F : C ↝ D) [has_right_adjoint F] :
  preserves_initial_object F :=
left_adjoint_preserves_initial_object (has_right_adjoint.adj F)

instance has_right_adjoint.preserves_pushouts (F : C ↝ D) [has_right_adjoint F] :
  preserves_pushouts F :=
left_adjoint_preserves_pushout (has_right_adjoint.adj F)

end category_theory
