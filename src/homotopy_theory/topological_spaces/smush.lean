import algebra.module
import topology.instances.real
import tactic.ring

import .tactic

/-

Construction of a homeomorphism of pairs
(Dⁿ, Sⁿ⁻¹) ⊗ (I, {0}) ≅ (Dⁿ, ∅) ⊗ (I, {0}).
See [tom Dieck, Algebraic Topology, Example 2.3.6].

Rather than specialize in ℝⁿ, we work in an arbitrary normed ℝ-linear
space V. Normed linear spaces are not yet in mathlib, so we just list
the structure and axioms we need on V.

-/

namespace homotopy_theory.topological_spaces.smush

class admissible (R : out_param Type) [discrete_linear_ordered_field R] (V : Type) extends has_scalar R V :=
(mul_smul' : ∀(r s : R) (x : V), (r * s) • x = r • s • x)
(one_smul' : ∀x : V, (1 : R) • x = x)
(norm : V → R)
(norm_nonneg : ∀x : V, 0 ≤ norm x)
(norm_mul : ∀r (x : V), norm (r • x) = abs r * norm x)

namespace construction
section

parameters {R : Type} [discrete_linear_ordered_field R]
parameters {V : Type} [@admissible R _ V]
open admissible

@[reducible] def I := {r : R // 0 ≤ r ∧ r ≤ 1}

local notation `norm` := (@admissible.norm R _ V _)

@[reducible] def unit_disk : Type := {v : V // norm v ≤ 1}
local notation `D` := unit_disk

def α : D × I → { r : R // r ≠ 0 } :=
λ p, ⟨max (2 * norm p.1.val) (2 - p.2.val),
  ne_of_gt $ gt_of_ge_of_gt (le_max_right _ _) $ sub_pos_of_lt $
  lt_of_le_of_lt p.2.property.right one_lt_two⟩

lemma α_ge_one {p} : (α p).val ≥ 1 :=
le_trans
  (le_sub_iff_add_le.mpr $ le_sub_iff_add_le'.mp $
    by norm_num; exact p.2.property.right)
  (le_max_right _ _)

lemma α_le_two {p} : (α p).val ≤ 2 :=
max_le
  (by convert mul_le_mul_of_nonneg_left p.1.property _; norm_num)
  ((sub_le_self_iff _).mpr p.2.property.left)

def H : D × I → D × I :=
λ p, begin
  refine (⟨((α p).val⁻¹ * (1 + p.2.val)) • p.1.val, _⟩, ⟨2 - (α p).val, _⟩),
  { rw [norm_mul, abs_of_nonneg, mul_assoc, ←div_eq_inv_mul, div_le_one_iff_le, α],
    exact calc
      (1 + p.2.val) * norm p.1.val
        ≤ (1 + 1) * norm p.1.val    : mul_le_mul_of_nonneg_right (add_le_add_left p.2.property.right _) (norm_nonneg _)
    ... = 2 * norm p.1.val          : by norm_num
    ... ≤ α p                       : le_max_left _ _,
    exact lt_of_lt_of_le zero_lt_one α_ge_one,
    apply mul_nonneg,
    apply inv_nonneg.mpr,
    exact le_trans zero_le_one α_ge_one,
    exact le_trans zero_le_one (le_add_of_nonneg_right p.2.property.left) },
  { split,
    exact sub_nonneg_of_le α_le_two,
    apply sub_le_of_sub_le,
    convert α_ge_one,
    norm_num }
end

def v : D × I → D × I :=
λ p, (p.1, ⟨1 - p.2.val, sub_nonneg_of_le p.2.property.right, sub_le_self _ p.2.property.left⟩)

lemma αvH (p : D × I) : (α (v (H p))).val = 1 + p.2.val :=
let ⟨x, t⟩ := p in
begin
  dsimp [H, v, α, -smul_eq_mul],
  rw norm_mul,
  cases le_total (2 * norm x.val) (2 + -t.val) with h1 h2,
  { rw max_eq_right h1,
    convert max_eq_right _ using 1,
    { ring },             -- ??
    { exact calc
        2 * (abs ((2 + -t.val)⁻¹ * (1 + t.val)) * norm (x.val))
          = (2 * norm x.val) * abs ((2 + -t.val)⁻¹ * (1 + t.val))  : by ac_refl
      ... ≤ (2 + -t.val) * abs ((2 + -t.val)⁻¹ * (1 + t.val))      : mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      ... = 1 + t.val                                              : begin
              have : 2 - t.val > 0, from sub_pos_of_lt (lt_of_le_of_lt t.property.right (by norm_num)),
              rw [abs_mul, abs_of_nonneg, abs_of_nonneg, ←mul_assoc, mul_inv_cancel, one_mul],
              swap, exact le_trans zero_le_one (le_add_of_nonneg_right t.property.left),
              all_goals { rw ←sub_eq_add_neg },
              exact ne_of_gt this,
              exact inv_nonneg.mpr (le_of_lt this)
            end
      ... = _                                                      : by ring } },
  { rw max_eq_left h2,
    have : 2 * (abs ((2 * norm (x.val))⁻¹ * (1 + t.val)) * norm (x.val)) = 1 + t.val,
    { symmetry,
      rw [abs_mul, abs_of_nonneg, abs_of_nonneg],
      exact calc
        1 + t.val
          = (2 * norm x.val) * (2 * norm x.val)⁻¹ * (1 + t.val) : begin
              rw [mul_inv_cancel, one_mul],
              refine ne_of_gt (lt_of_lt_of_le _ h2),
              rw [←sub_eq_add_neg, sub_pos],
              exact lt_of_le_of_lt t.property.right (by norm_num)
            end
      ... = _ : by ring,
      exact le_trans zero_le_one (le_add_of_nonneg_right t.property.left),
      exact inv_nonneg.mpr (mul_nonneg (by norm_num) (norm_nonneg _))
    },
    rw this,
    apply max_eq_left,
    rw [←sub_eq_add_neg, iff.intro sub_le_of_sub_le sub_le_of_sub_le] at h2,
    apply le_add_of_sub_left_le,
    convert h2 using 1, ring }
end

lemma vHvH (p : D × I) : v (H (v (H p))) = p :=
begin
  rw [H] { occs := occurrences.pos [1] },
  rw [v] { occs := occurrences.pos [1] },
  apply prod.ext; apply subtype.eq; dsimp; rw αvH p,
  { rw [H, v], dsimp,
    transitivity ((1 + (p.snd).val)⁻¹ * (1 + (p.snd).val)) • ((α p).val * ((α p).val)⁻¹) • (p.fst).val,
    { rw [←admissible.mul_smul', ←admissible.mul_smul'], congr' 1, ring },
    { rw [mul_inv_cancel, inv_mul_cancel, admissible.one_smul', admissible.one_smul'],
      exact ne_of_gt (lt_of_lt_of_le (by norm_num) (le_add_of_nonneg_right p.2.property.left)),
      exact (α p).property } },
  { ring }
end

lemma vv (p : D × I) : v (v p) = p :=
begin
  dsimp [v], apply prod.ext, { refl }, { apply subtype.eq, dsimp, ring }
end

lemma HvHv (p : D × I) : H (v (H (v p))) = p :=
have v (v (H (v (H (v p))))) = v (v p), by rw vHvH,
by rwa [vv, vv] at this

lemma eq_iff_le_of_ge {a b : R} (h : a ≥ b) : a = b ↔ a ≤ b :=
iff.intro le_of_eq (assume h', le_antisymm h' h)

lemma eq_iff_ge_of_le {a b : R} (h : a ≤ b) : a = b ↔ a ≥ b :=
iff.intro ge_of_eq (assume h', le_antisymm h h')

lemma Ht0 (p : D × I) : (H p).2.val = 0 ↔ norm p.1.val = 1 ∨ p.2.val = 0 :=
begin
  rw [H, sub_eq_zero, eq_iff_le_of_ge α_le_two, α, eq_iff_ge_of_le p.1.property, eq_iff_le_of_ge p.2.property.left, le_max_iff],
  apply or_congr,
  { exact le_mul_iff_one_le_right (by norm_num) },
  { rw le_sub_iff_add_le, convert add_le_add_iff_left (2 : R) using 2, simp }
end

end
end construction

section continuity

noncomputable theory

class admissible' (V : Type) [topological_space V] extends admissible ℝ V :=
(continuous_smul : continuous (λ p : ℝ × V, p.1 • p.2))
(continuous_norm : continuous (admissible.norm : V → ℝ))

parameters (V : Type) [topological_space V] [admissible' V]
@[reducible] def I := @construction.I ℝ _
@[reducible] def unit_disk := @construction.unit_disk ℝ _ V _
local notation `D` := unit_disk

parameters {V}
def α : D × I → {r : ℝ // r ≠ 0} := @construction.α ℝ _ V _
def H : D × I → D × I := @construction.H ℝ _ V _
def v : D × I → D × I := @construction.v ℝ _ V _

lemma continuous_smul {β : Type*} [topological_space β]
  {f : β → ℝ} {g : β → V} (hf : continuous f) (hg : continuous g) :
  continuous (λx, f x • g x) :=
(admissible'.continuous_smul V).comp (hf.prod_mk hg)

@[tidy] meta def apply_continuous_smul := `[refine continuous_smul _ _]

@[back] lemma continuous_norm : continuous (admissible.norm : V → ℝ) :=
admissible'.continuous_norm V

lemma continuous_α : continuous α := by unfold α; continuity

section
local attribute [elab_simple] continuous.comp
@[back] lemma continuous_α_inv : continuous (λ p, (α p).val⁻¹) :=
continuous.comp real.continuous_inv' continuous_α
end

lemma continuous_H : continuous H := by unfold H; continuity

lemma continuous_v : continuous v := by unfold v; continuity

lemma continuous_vHv : continuous (v ∘ H ∘ v) :=
continuous_v.comp (continuous_H.comp continuous_v)

def H_equiv : (D × I) ≃ (D × I) :=
{ to_fun := H,
  inv_fun := v ∘ H ∘ v,
  left_inv := construction.vHvH,
  right_inv := construction.HvHv }

def unit_sphere_in_disk : set unit_disk := {v | admissible.norm v.val = (1 : ℝ)}

lemma Ht0 : {p : D × I | p.1 ∈ unit_sphere_in_disk ∨ p.2.val = 0} = H ⁻¹' {p | false ∨ p.2.val = 0} :=
set.ext $ λ p, by convert (construction.Ht0 p).symm; simp; refl

end continuity

instance : admissible' ℝ :=
{ mul_smul' := _root_.mul_smul,
  one_smul' := _root_.one_smul _,
  norm := abs,
  norm_nonneg := abs_nonneg,
  norm_mul := abs_mul,

  continuous_smul := continuous_mul',
  continuous_norm := real.continuous_abs }

end homotopy_theory.topological_spaces.smush
