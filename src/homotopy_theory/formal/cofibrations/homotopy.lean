import .cofibration_category
import .cylinder
import .lifting

universes u v

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.cofibrations
open precofibration_category cofibration_category

variables {C : Type u} [cat : category.{u v} C] [cofibration_category.{u v} C]
include cat

-- Homotopies in a cofibration category.

variables {a b : C} {j : a ⟶ b} {hj : is_cof j}

structure homotopy_on (c : relative_cylinder hj) {x : C} (f₀ f₁ : b ⟶ x) :=
(H : c.ob ⟶ x)
(Hi₀ : H ∘ c.i₀ = f₀)
(Hi₁ : H ∘ c.i₁ = f₁)

-- Two maps f₀, f₁ are homotopic rel j with respect to a chosen
-- cylinder object on j if there exists a homotopy from f₀ to f₁
-- defined on that cylinder.
def homotopic_wrt (c : relative_cylinder hj) {x : C} (f₀ f₁ : b ⟶ x) : Prop :=
nonempty (homotopy_on c f₀ f₁)

-- If x is fibrant, then any two cylinders define the same homotopy
-- rel j relation on maps b ⟶ x.
lemma homotopic_iff_of_embedding {c c' : relative_cylinder hj}
  (m : cylinder_embedding c c') {x : C} (hx : fibrant x) (f₀ f₁ : b ⟶ x) :
  homotopic_wrt c f₀ f₁ ↔ homotopic_wrt c' f₀ f₁ :=
iff.intro
  (assume ⟨⟨H, Hi₀, Hi₁⟩⟩,
    let ⟨H', hH'⟩ := fibrant_iff_rlp.mp hx m.acof_k H in
    ⟨⟨H', by rw ←m.hki₀; simp [hH', Hi₀], by rw ←m.hki₁; simp [hH', Hi₁]⟩⟩)
  (assume ⟨⟨H, Hi₀, Hi₁⟩⟩,
    ⟨⟨H ∘ m.k, by rw [←associativity, m.hki₀, Hi₀], by rw [←associativity, m.hki₁, Hi₁]⟩⟩)

lemma homotopic_iff (c₀ c₁ : relative_cylinder hj) {x : C} (hx : fibrant x) (f₀ f₁ : b ⟶ x) :
  homotopic_wrt c₀ f₀ f₁ ↔ homotopic_wrt c₁ f₀ f₁ :=
let ⟨c', m₀, m₁, ⟨⟩⟩ := exists_common_embedding c₀ c₁ in
(homotopic_iff_of_embedding m₀ hx f₀ f₁).trans
  (homotopic_iff_of_embedding m₁ hx f₀ f₁).symm

variables (hj)
def homotopic_rel {x} (f₀ f₁ : b ⟶ x) : Prop :=
∃ c : relative_cylinder hj, homotopic_wrt c f₀ f₁

variables {hj}
lemma homotopic_rel' (c : relative_cylinder hj) {x} (hx : fibrant x) (f₀ f₁ : b ⟶ x)
  (h : homotopic_rel hj f₀ f₁) : homotopic_wrt c f₀ f₁ :=
let ⟨c', hw⟩ := h in (homotopic_iff c' c hx f₀ f₁).mp hw

@[refl] lemma homotopic_rel.refl {x} (f : b ⟶ x) : homotopic_rel hj f f :=
let ⟨c⟩ := exists_relative_cylinder hj in
⟨c, ⟨⟨f ∘ c.p, by rw [←associativity, c.pi₀]; simp, by rw [←associativity, c.pi₁]; simp⟩⟩⟩

@[symm] lemma homotopic_rel.symm {x} {f₀ f₁ : b ⟶ x} :
  homotopic_rel hj f₀ f₁ → homotopic_rel hj f₁ f₀ :=
assume ⟨c, ⟨⟨H, Hi₀, Hi₁⟩⟩⟩,
⟨c.reverse, ⟨⟨H, by convert Hi₁; simp, by convert Hi₀; simp⟩⟩⟩

@[trans] lemma homotopic_rel.trans {x} {f₀ f₁ f₂ : b ⟶ x} :
  homotopic_rel hj f₀ f₁ → homotopic_rel hj f₁ f₂ → homotopic_rel hj f₀ f₂ :=
assume ⟨c₀, ⟨⟨H₀, H₀i₀, H₀i₁⟩⟩⟩ ⟨c₁, ⟨⟨H₁, H₁i₀, H₁i₁⟩⟩⟩,
⟨c₀.glue c₁,
  ⟨⟨(pushout_by_cof c₀.i₁ c₁.i₀ c₀.acof_i₁.1).is_pushout.induced H₀ H₁ (H₀i₁.trans H₁i₀.symm),
    by convert H₀i₀ using 1; simp, by convert H₁i₁ using 1; simp⟩⟩⟩

lemma homotopic_rel_is_equivalence {x : C} :
  equivalence (homotopic_rel hj : (b ⟶ x) → (b ⟶ x) → Prop) :=
⟨homotopic_rel.refl,
 λ f₀ f₁, homotopic_rel.symm,
 λ f₀ f₁ f₂, homotopic_rel.trans⟩

end homotopy_theory.cofibrations
