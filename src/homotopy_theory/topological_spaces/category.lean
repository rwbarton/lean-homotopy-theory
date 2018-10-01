import analysis.topology.topological_space
import analysis.topology.continuity
import category_theory.base
import category_theory.functor_category

import .tactic

open category_theory

universe u

namespace homotopy_theory.topological_spaces

structure Top : Type (u+1) :=
(carrier : Type u)
(topology : topological_space carrier)

namespace Top

local notation `Top` := Top.{u}

instance : has_coe_to_sort Top :=
{ S := Type u, coe := λ X, X.carrier }

instance (X : Top) : topological_space X.carrier := X.topology

def continuous_map (X Y : Top) : Type u :=
{ f : X.carrier → Y.carrier // continuous f }

instance {X Y : Top} : has_coe_to_fun (continuous_map X Y) :=
{ F := λ _, X → Y, coe := λ f, f.val }

instance : category Top :=
{ hom := continuous_map,
  id := λ X, ⟨id, by continuity⟩,
  comp := λ _ _ _ f g, ⟨g.val ∘ f.val, by continuity⟩ }

protected def mk_ob (α : Type u) [t : topological_space α] : Top := ⟨α, t⟩
protected def mk_hom {X Y : Top} (f : X → Y) (hf : continuous f . continuity') : X ⟶ Y := subtype.mk f hf
@[extensionality] protected def hom_eq {X Y : Top} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
subtype.eq (funext h)
protected lemma hom_eq2 {X Y : Top} {f g : X ⟶ Y} : f = g ↔ f.val = g.val := by cases f; cases g; simp
protected def hom_congr {X Y : Top} {f g : X ⟶ Y} : f = g → ∀ x, f x = g x :=
by intros e x; rw e


section terminal

protected def point : Top := @Top.mk_ob punit ⊥
notation `*` := Top.point

protected def point_induced (A : Top) : A ⟶ * :=
Top.mk_hom (λ _, punit.star) (by continuity)

end terminal

protected def const {A X : Top} (x : X) : A ⟶ X :=
Top.mk_hom (λ a, x) (by continuity)


section product

-- TODO: Generalize all the following definitions using a `has_product` class

protected def prod (X Y : Top) : Top :=
Top.mk_ob (X.carrier × Y.carrier)

protected def pr₁ {X Y : Top} : Top.prod X Y ⟶ X :=
Top.mk_hom (λ p, p.1)

protected def pr₂ {X Y : Top} : Top.prod X Y ⟶ Y :=
Top.mk_hom (λ p, p.2)

-- TODO: The (by continuity) argument ought to be supplied
-- automatically by auto_param, but for some reason elaboration goes
-- wrong without it
protected def prod_maps {X X' Y Y' : Top} (f : X ⟶ X') (g : Y ⟶ Y') :
  Top.prod X Y ⟶ Top.prod X' Y' :=
Top.mk_hom (λ p, (f p.1, g p.2)) (by continuity)

protected def prod_pt {X Y : Top} (y : Y) : X ⟶ Top.prod X Y :=
Top.mk_hom (λ x, (x, y)) (by continuity)

protected def product_by (Y : Top) : Top ↝ Top :=
{ obj := λ X, Top.prod X Y,
  map' := λ X X' f, Top.prod_maps f (𝟙 Y) }

notation `-×`:35 Y:34 := Top.product_by Y

protected def product_by_trans {Y Y' : Top} (g : Y ⟶ Y') : -×Y ⟶ -×Y' :=
{ app := λ X, Top.prod_maps (𝟙 X) g }

protected def prod_pt_trans {Y : Top} (y : Y) : functor.id _ ⟶ -×Y :=
{ app := λ X, Top.prod_pt y }

protected def pr₁_trans {Y : Top} : -×Y ⟶ functor.id _ :=
{ app := λ X, Top.pr₁ }

end product

end «Top»

end homotopy_theory.topological_spaces
