import topology.maps
import category_theory.base
import category_theory.functor_category
import topology.category.Top.basic

open category_theory

universe u

namespace homotopy_theory.topological_spaces

namespace Top

local notation `Top` := Top.{u}

protected def mk_ob (α : Type u) [t : topological_space α] : Top := ⟨α, t⟩
protected def mk_hom {X Y : Top} (f : X → Y) (hf : continuous f . tactic.interactive.continuity') : X ⟶ Y :=
continuous_map.mk f hf
@[ext] protected def hom_eq {X Y : Top} {f g : X ⟶ Y} (h : ∀ x, f x = g x) : f = g :=
continuous_map.ext h
protected lemma hom_eq2 {X Y : Top} {f g : X ⟶ Y} : f = g ↔ f.to_fun = g.to_fun :=
by { cases f, cases g, split; cc }
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
Top.mk_ob (X.α × Y.α)

protected def pr₁ {X Y : Top} : Top.prod X Y ⟶ X :=
Top.mk_hom (λ p, p.1) (by continuity!)

protected def pr₂ {X Y : Top} : Top.prod X Y ⟶ Y :=
Top.mk_hom (λ p, p.2) (by continuity!)

-- TODO: The (by continuity) argument ought to be supplied
-- automatically by auto_param, but for some reason elaboration goes
-- wrong without it
protected def prod_maps {X X' Y Y' : Top} (f : X ⟶ X') (g : Y ⟶ Y') :
  Top.prod X Y ⟶ Top.prod X' Y' :=
Top.mk_hom (λ p, (f p.1, g p.2)) (by continuity!)

protected def prod_pt {X Y : Top} (y : Y) : X ⟶ Top.prod X Y :=
Top.mk_hom (λ x, (x, y)) (by continuity)

protected def product_by (Y : Top) : Top ↝ Top :=
{ obj := λ X, Top.prod X Y,
  map := λ X X' f, Top.prod_maps f (𝟙 Y) }

notation `-×`:35 Y:34 := Top.product_by Y

protected def product_by_trans {Y Y' : Top} (g : Y ⟶ Y') : -×Y ⟶ -×Y' :=
{ app := λ X, Top.prod_maps (𝟙 X) g }

protected def prod_pt_trans {Y : Top} (y : Y) : functor.id _ ⟶ -×Y :=
{ app := λ X, Top.prod_pt y }

protected def pr₁_trans {Y : Top} : -×Y ⟶ functor.id _ :=
{ app := λ X, Top.pr₁ }

end product

section subtype

/-- The hom sets of Top used to be defined using `subtype`;
this provides the equivalence to the old definition. -/
protected def hom_equiv_subtype (X Y : Top) :
  (X ⟶ Y) ≃ {f : X → Y // continuous f} :=
{ to_fun := λ p, ⟨p.1, p.2⟩,
  inv_fun := λ p, ⟨p.1, p.2⟩,
  left_inv := λ p, by cases p; refl,
  right_inv := λ p, by cases p; refl }

end subtype

end «Top»

end homotopy_theory.topological_spaces
