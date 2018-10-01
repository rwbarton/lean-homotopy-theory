import .category
import .homeomorphism

open category_theory
local notation f ` ∘ `:80 g:80 := g ≫ f

universe u

namespace homotopy_theory.topological_spaces
open Top

structure Top_ptd : Type (u+1) :=
(space : Top.{u})
(pt : space)

namespace Top_ptd

local notation `Top_ptd` := Top_ptd.{u}

instance : has_coe Top_ptd Top :=
⟨λ X, X.space⟩

instance : has_coe_to_sort Top_ptd :=
{ S := Type u, coe := λ X, X.space.carrier }

def ptd_map (X Y : Top_ptd) : Type u :=
{ f : X.space ⟶ Y.space // (f : X.space ⟶ Y.space) X.pt = Y.pt }

instance {X Y : Top_ptd} : has_coe_to_fun (ptd_map X Y) :=
{ F := λ _, X → Y, coe := λ f, f.val.val }

instance : category Top_ptd :=
{ hom := ptd_map,
  id := λ X, ⟨𝟙 X, rfl⟩,
  comp := λ _ _ _ f g,
    ⟨g.val ∘ f.val,
     show g.val (f.val _) = _, by rw [f.property, g.property]⟩ }

protected def mk_ob (X : Top) (x : X) : Top_ptd := ⟨X, x⟩
protected def mk_hom {X Y : Top_ptd} (f : X.space ⟶ Y.space)
  (hf : f X.pt = Y.pt) : X ⟶ Y :=
subtype.mk f hf

protected def mk_iso {X Y : Top_ptd} (i : Top.homeomorphism X.space Y.space)
  (hi : i X.pt = Y.pt) : X ≅ Y :=
{ hom := ⟨i, hi⟩,
  inv := ⟨i.inv, begin
      rw ←hi, change i.equiv.symm (i.equiv X.pt) = X.pt, simp
    end⟩,
  hom_inv_id' := subtype.eq i.hom_inv_id,
  inv_hom_id' := subtype.eq i.inv_hom_id }

protected def mk_iso' {X Y : Top} (i : Top.homeomorphism X Y) (x : X) :
  Top_ptd.mk_ob X x ≅ Top_ptd.mk_ob Y (i x) :=
Top_ptd.mk_iso i rfl

end «Top_ptd»

end homotopy_theory.topological_spaces
