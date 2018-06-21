import categories.types
import homotopy_theory.formal.i_category.homotopy_classes
import homotopy_theory.formal.i_category.drag

import .disk_sphere
import .i_category

noncomputable theory

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open homotopy_theory.cylinder
open Top
local notation `Top` := Top.{0}
local notation `Set` := Type.{0}

local notation `[` A `, ` X `]` := homotopy_classes A X

-- We define π₀(X) as the set of homotopy classes of maps from a point
-- to X. π₀ is a functor from Top to Set, namely the functor
-- corepresented on the homotopy category by *.

def π₀ : Top ↝ Set :=
{ onObjects := λ X, [*, X], onMorphisms := λ X Y f x, ⟦f⟧ ∘ x }

-- We define πₙ(X, x) as the set of homotopy classes of maps D[n] → X
-- which send S[n-1] to x, rel S[n-1]. Can't define it as a functor
-- yet, since we don't have a category of pointed topological spaces.

def π_ (n : ℕ) (X : Top) (x : X) : Set :=
homotopy_classes_extending_rel (sphere_disk_incl n) (sphere_disk_cofibration n) (Top.const x)

def π_induced (n : ℕ) {X Y : Top} (x : X) (f : X ⟶ Y) : π_ n X x ⟶ π_ n Y (f x) :=
hcer_induced f

-- Change-of-basepoint maps.

def path {X : Top} (x x' : X) : Type := homotopy (Top.const x : * ⟶ X) (Top.const x' : * ⟶ X)

def path.induced {X Y : Top} (f : X ⟶ Y) {x x' : X} (γ : path x x') : path (f x) (f x') :=
γ.congr_left f

def change_of_basepoint (n : ℕ) {X : Top} {x x' : X} (γ : path x x') : π_ n X x ≃ π_ n X x' :=
drag_equiv (γ.congr_right S[n-1].point_induced)

lemma change_of_basepoint_induced (n : ℕ) {X Y : Top} {x x' : X} (γ : path x x') (f : X ⟶ Y) (a) :
  π_induced n x' f (change_of_basepoint n γ a) =
  (change_of_basepoint n (γ.induced f)) (π_induced n x f a) :=
drag_equiv_induced _ _ _

end homotopy_theory.topological_spaces
