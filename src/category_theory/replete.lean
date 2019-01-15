import category_theory.base
import category_theory.isomorphism

open category_theory
open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

universes v u

namespace category_theory

variables (C : Type u) [cat : category.{v} C]
include cat

class wide_subcategory (D : Π {a b : C}, (a ⟶ b) → Prop) : Prop :=
(mem_id {} : ∀ (a : C), D (𝟙 a))
(mem_comp {} : ∀ {a b c : C} {f : a ⟶ b} {g : b ⟶ c}, D f → D g → D (g ∘ f))
export wide_subcategory (mem_id mem_comp)

class replete_wide_subcategory D extends wide_subcategory.{v} C D : Prop :=
(mem_iso {} : ∀ {a b : C} (i : iso a b), D i.hom)
export replete_wide_subcategory (mem_iso)

variables {C}
-- mem_id is redundant when we have mem_iso.
lemma replete_wide_subcategory.mk' {D : Π ⦃a b : C⦄, (a ⟶ b) → Prop}
  (mem_iso : ∀ {a b : C} (i : iso a b), D i.hom)
  (mem_comp : ∀ {a b c : C} {f : a ⟶ b} {g : b ⟶ c}, D f → D g → D (g ∘ f)) :
  replete_wide_subcategory.{v} C D :=
{ mem_id := λ a, mem_iso (iso.refl a),
  mem_comp := @mem_comp,
  mem_iso := @mem_iso }

variables {D : Π ⦃a b : C⦄, (a ⟶ b) → Prop} [replete_wide_subcategory.{v} C D]

lemma mem_of_mem_comp_left {a b c : C} {f : a ⟶ b} (i : iso b c)
  (h : D (i.hom ∘ f)) : D f :=
by convert mem_comp h (mem_iso i.symm); simp

lemma mem_of_mem_comp_right {a b c : C} {f : b ⟶ c} (i : iso a b)
  (h : D (f ∘ i.hom)) : D f :=
by convert mem_comp (mem_iso i.symm) h; simp

lemma mem_iff_mem_of_isomorphic {a b a' b' : C} {f : a ⟶ b} {f' : a' ⟶ b'}
  (i : iso a a') (j : iso b b')
  (e : j.hom ∘ f = f' ∘ i.hom) : D f ↔ D f' :=
iff.intro
  (assume h, have D (j.hom ∘ f), from mem_comp h (mem_iso j),
    by rw e at this; exact mem_of_mem_comp_right i this)
  (assume h, have D (f' ∘ i.hom), from mem_comp (mem_iso i) h,
    by rw ←e at this; exact mem_of_mem_comp_left j this)

end category_theory
