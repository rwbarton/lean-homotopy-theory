import category_theory.base
import category_theory.colimits
import category_theory.adjunction
import data.bij_on

open set

universes v₁ v₂ u₁ u₂

namespace category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

variables {C : Type u₁} [catC : category.{v₁+1} C]
variables {D : Type u₂} [catD : category.{v₂+1} D]
include catC catD

class preserves_initial_object (F : C ↝ D) :=
(Is_initial_object_of_Is_initial_object :
  Π {a : C}, Is_initial_object.{v₁} a → Is_initial_object.{v₂} (F.obj a))

class preserves_coproducts (F : C ↝ D) :=
(Is_coproduct_of_Is_coproduct :
  Π {a₀ a₁ b : C} {f₀ : a₀ ⟶ b} {f₁ : a₁ ⟶ b},
  Is_coproduct f₀ f₁ → Is_coproduct (F &> f₀) (F &> f₁))

class preserves_pushouts (F : C ↝ D) :=
(Is_pushout_of_Is_pushout :
  Π {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c},
  Is_pushout f₀ f₁ g₀ g₁ → Is_pushout (F &> f₀) (F &> f₁) (F &> g₀) (F &> g₁))

section left_adjoint

variables {F : C ↝ D} {G : D ↝ C} (adj : F ⊣ G)

def left_adjoint_preserves_initial_object : preserves_initial_object F :=
⟨λ a ai, Is_initial_object.mk $ λ x,
  Is_equiv.mk ((adj.hom_equiv a x).trans (ai.universal (G.obj x)).e)
    (by ext; refl)⟩

-- TODO: show left adjoints preserve coproducts

local notation [parsing_only] a ` ~~ ` b := Bij_on _ a b

def left_adjoint_preserves_pushout : preserves_pushouts F :=
⟨λ a b₀ b₁ c f₀ f₁ g₀ g₁ po, Is_pushout.mk $ λ x,
  have _ := calc
    (univ : set (F.obj c ⟶ x))
      ~~ (univ : set (c ⟶ G.obj x))
      : Bij_on.of_equiv (adj.hom_equiv c x)
  ... ~~ {p : (b₀ ⟶ G.obj x) × (b₁ ⟶ G.obj x) | p.1 ∘ f₀ = p.2 ∘ f₁}
      : po.universal (G.obj x)
  ... ~~ {p : (b₀ ⟶ G.obj x) × (b₁ ⟶ G.obj x) | _}
      :
  begin
    convert Bij_on.refl _, funext p, cases p with p1 p2,
    change
      ((adj.hom_equiv b₀ x).symm p1 ∘ F &> f₀ =
       (adj.hom_equiv b₁ x).symm p2 ∘ F &> f₁) =
      (p1 ∘ f₀ = p2 ∘ f₁),
    transitivity
      ((adj.hom_equiv a x).symm (p1 ∘ f₀) =
       (adj.hom_equiv a x).symm (p2 ∘ f₁)),
    { rw adj.hom_equiv_naturality_left_symm,
      rw adj.hom_equiv_naturality_left_symm },
    { simp }
  end
  ... ~~ {p : (F.obj b₀ ⟶ x) × (F.obj b₁ ⟶ x) | p.1 ∘ (F &> f₀) = p.2 ∘ (F &> f₁)}
      : Bij_on.restrict''
          (Bij_on.prod'
            (Bij_on.of_equiv (adj.hom_equiv b₀ x).symm)
            (Bij_on.of_equiv (adj.hom_equiv b₁ x).symm))
          (λ p, p.1 ∘ (F &> f₀) = p.2 ∘ (F &> f₁)),
  begin
    convert this,
    funext k,
    change (k ∘ F &> g₀, k ∘ F &> g₁) =
      ((adj.hom_equiv b₀ x).symm (adj.hom_equiv c x k ∘ g₀),
       (adj.hom_equiv b₁ x).symm (adj.hom_equiv c x k ∘ g₁)),
    rw adj.hom_equiv_naturality_left_symm,
    rw adj.hom_equiv_naturality_left_symm,
    simp
  end⟩

end left_adjoint

namespace adjunction

instance is_left_adjoint.preserves_initial_object (F : C ↝ D) [h : is_left_adjoint F] :
  preserves_initial_object F :=
left_adjoint_preserves_initial_object h.adj

instance is_left_adjoint.preserves_pushouts (F : C ↝ D) [h : is_left_adjoint F] :
  preserves_pushouts F :=
left_adjoint_preserves_pushout h.adj

end adjunction

end category_theory
