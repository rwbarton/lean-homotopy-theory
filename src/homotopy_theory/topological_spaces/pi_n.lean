import categories.types
import homotopy_theory.formal.i_category.homotopy_classes

import .disk_sphere
import .i_category

noncomputable theory

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
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

def π_induced (n : ℕ) {X Y : Top} {x : X} (f : X ⟶ Y) : π_ n X x ⟶ π_ n Y (f x) :=
hcer_induced (sphere_disk_incl n) (sphere_disk_cofibration n) (Top.const x) f

end homotopy_theory.topological_spaces
