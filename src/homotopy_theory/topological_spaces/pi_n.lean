import category_theory.isomorphism
import category_theory.types
import homotopy_theory.formal.i_category.homotopy_classes
import homotopy_theory.formal.i_category.drag

import .disk_sphere
import .i_category
import .pointed

noncomputable theory

open category_theory (hiding is_iso)
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open homotopy_theory.cylinder
open homotopy_theory.weak_equivalences
open Top
local notation `Top` := Top.{0}
local notation `Set` := Type.{0}

local notation `[` A `, ` X `]` := homotopy_classes A X

-- We define π₀(X) as the set of homotopy classes of maps from a point
-- to X. π₀ is a functor from Top to Set, namely the functor
-- corepresented on the homotopy category by *.

def π₀ : Top ↝ Set :=
{ obj := λ X, [*, X], map := λ X Y f x, ⟦f⟧ ∘ x }

-- The "based n-sphere" is the quotient of D[n] by its boundary S[n-1].
def based_sphere (n : ℕ) : Top :=
quotient_space (sphere_disk_incl n)

def based_sphere_basepoint (n : ℕ) : Top.point ⟶ based_sphere n :=
Top.const (quotient_space.pt _)

-- We define πₙ(X, x) as the set of homotopy classes of maps D[n]/S[n-1] → X
-- which send the basepoint to x, rel the basepoint.

def π_ (n : ℕ) (X : Top) (x : X) : Set :=
homotopy_classes_extending_rel (based_sphere_basepoint n)
  (precofibration_category.pushout_is_cof (quotient_space.is_pushout _) (sphere_disk_cofibration n))
  (Top.const x)

def π_induced (n : ℕ) {X Y : Top} (x : X) (f : X ⟶ Y) : π_ n X x ⟶ π_ n Y (f x) :=
hcer_induced f

-- Non-Top_ptd-aware versions of functoriality.
--
-- This should really be an application of a lemma `hcer_induced_id`,
-- but writing down the type of that lemma is more annoying than just
-- writing the one-line proof here.
lemma π_induced_id (n : ℕ) {X : Top} (x : X) : π_induced n x (𝟙 X) = id :=
by funext a; induction a using quot.ind; change ⟦_⟧ = _; simp; refl

-- Similarly.
lemma π_induced_comp (n : ℕ) {X Y Z : Top} (x : X) (f : X ⟶ Y) (g : Y ⟶ Z) :
  π_induced n x (g ∘ f) = π_induced n (f x) g ∘ π_induced n x f :=
by funext a; induction a using quot.ind; change ⟦_⟧ = ⟦_⟧; simp; refl

def π (n : ℕ) : Top_ptd ↝ Set :=
{ obj := λ Xx, π_ n Xx.space Xx.pt,
  map := λ Xx Yy f,
    by convert π_induced n Xx.pt f.val; rw f.property,
  map_id' := assume Xx, π_induced_id n Xx.pt,
  map_comp' := assume Xx Yy Zz f g, begin
    -- This is tricky because the action of π on a morphism f involves
    -- recursion on the equality `f.property` : f x = y. We need to
    -- arrange for z and then y to be "free", i.e., not mentioned
    -- earlier in the context, so that we can match on the equality
    -- proofs using `subst`.
    rcases Xx with ⟨X, x⟩,
    rcases Yy with ⟨Y, y⟩,
    rcases Zz with ⟨Z, z⟩,
    rcases g with ⟨g, hg⟩, change Y ⟶ Z at g, change g y = z at hg,
    rcases f with ⟨f, hf⟩, change X ⟶ Y at f, change f x = y at hf,
    subst z, subst y,
    -- Now we can apply the simple version
    exact π_induced_comp n x f g
  end }

-- Change-of-basepoint maps.

def path {X : Top} (x x' : X) : Type := homotopy (Top.const x : * ⟶ X) (Top.const x' : * ⟶ X)

def path.induced {X Y : Top} (f : X ⟶ Y) {x x' : X} (γ : path x x') : path (f x) (f x') :=
γ.congr_left f

def path_of_homotopy {X Y : Top} (x : X) {f f' : X ⟶ Y} (H : homotopy f f') :
  path (f x) (f' x) :=
H.congr_right (Top.const x)

-- TODO: Move this
def iso_of_equiv {X Y : Set} (e : X ≃ Y) : X ≅ Y :=
{ hom := e.to_fun,
  inv := e.inv_fun,
  hom_inv_id' := funext e.left_inv,
  inv_hom_id' := funext e.right_inv }

def change_of_basepoint (n : ℕ) {X : Top} {x x' : X} (γ : path x x') : π_ n X x ≅ π_ n X x' :=
iso_of_equiv $ drag_equiv γ

lemma change_of_basepoint_induced (n : ℕ) {X Y : Top} {x x' : X} (γ : path x x') (f : X ⟶ Y) :
  π_induced n x' f ∘ (change_of_basepoint n γ).hom =
  (change_of_basepoint n (γ.induced f)).hom ∘ π_induced n x f :=
funext $ drag_equiv_induced _ _

lemma π₀_induced_homotopic {X Y : Top} {f f' : X ⟶ Y} (h : f ≃ f') :
  π₀ &> f = π₀ &> f' :=
have ⟦f⟧ = ⟦f'⟧, from quotient.sound h,
funext $ λ x, show ⟦f⟧ ∘ x = ⟦f'⟧ ∘ x, by rw this

-- Homotopic maps induce the same map on πₙ, up to change-of-basepoint
-- identifications.
lemma π_induced_homotopic (n : ℕ) {X Y : Top} (x : X) {f f' : X ⟶ Y} (H : homotopy f f') :
  (change_of_basepoint n (path_of_homotopy x H)).hom ∘ π_induced n x f =
  π_induced n x f' :=
funext $ hcer_induced_homotopic _

lemma π_induced_homotopic_id (n : ℕ) {X : Top} (x : X) {f : X ⟶ X} (h : 𝟙 X ≃ f) :
  is_iso (π_induced n x f) :=
let ⟨H⟩ := h in
begin
  rw [←π_induced_homotopic n x H, π_induced_id],
  apply iso_iso
end

end homotopy_theory.topological_spaces
