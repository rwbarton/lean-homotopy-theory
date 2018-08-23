import category_theory.category

namespace category_theory

universes u v

class groupoid (Obj : Type u) extends category.{u v} Obj :=
(inv : Π {X Y : Obj}, (X ⟶ Y) → (Y ⟶ X))
(inv_comp : ∀ {X Y : Obj} (f : X ⟶ Y), comp (inv f) f = id Y . obviously)
(comp_inv : ∀ {X Y : Obj} (f : X ⟶ Y), comp f (inv f) = id X . obviously)

notation f `⁻¹` := groupoid.inv f

restate_axiom groupoid.inv_comp
restate_axiom groupoid.comp_inv

attribute [simp] groupoid.inv_comp_lemma groupoid.comp_inv_lemma

abbreviation large_groupoid (C : Type (u+1)) : Type (u+1) := groupoid.{u+1 u} C
abbreviation small_groupoid (C : Type u) : Type (u+1) := groupoid.{u u} C

end category_theory
