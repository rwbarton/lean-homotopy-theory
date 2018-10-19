import data.fin order.basic tactic.split_ifs
import category_theory.base

open category_theory

def simplex_category := ℕ

local notation `Δ` := simplex_category
local notation `[`n`]` := fin (n + 1)

instance : has_coe_to_sort (Δ) :=
{S := Type, coe := λ n, [n]}

/- Nota bene: We will abuse the notation (n : Δ)
   to denote what a mathematician would call [n].
-/

/- This defines the set of monotone maps. The best solution
   is probably to rename `monotone` to `is_monotone,
   so that we can use `monotone` instead of the following
   `order_preserving_map`.
-/
def order_preserving_map (m n : Δ) :=
{f : m → n // monotone f}

instance {m n : Δ} : has_coe_to_fun (order_preserving_map m n) :=
{ F := λ _, m → n, coe := λ f, f.val }

instance : category Δ :=
{ hom := order_preserving_map, --λ m n : Δ, {f : m → n // monotone f},
  id := λ X, ⟨id, monotone_id⟩,
  comp := λ _ _ _ f g, ⟨g.val ∘ f.val, monotone_comp f.2 g.2⟩ }

namespace simplex_category

protected lemma hom_eq2 {m n : Δ} {f g : m ⟶ n} : f = g ↔ f.val = g.val := by cases f; cases g; simp

variables {n : Δ}

/-- The i-th face map from [n] to [n+1] -/
def δ (i : [n+1]) : n ⟶ ((n + 1) : ℕ) :=
⟨λ a, if h : i.val ≤ a.val then a.succ else a.cast_succ,
  begin
    intros a b H,
    dsimp,
    split_ifs with ha hb,
    { show a.succ.val ≤ b.succ.val,
      simpa using nat.succ_le_succ H },
    { exfalso,
      exact hb (nat.le_trans ha H) },
    { show a.val ≤ b.succ.val,
      simpa using nat.le_trans H (nat.le_succ b) },
    { exact H }
  end⟩

/-- The i-th degeneracy map from [n+1] to [n] -/
def σ (i : [n]) : @category.hom Δ _ ((n + 1) : ℕ) n :=
⟨λ a, if h : a.val ≤ i.val
    then ⟨a.val, lt_of_le_of_lt h i.is_lt⟩
    else ⟨a.val.pred,
      (nat.sub_lt_right_iff_lt_add (lt_of_le_of_lt i.val.zero_le (not_le.mp h))).mpr a.is_lt⟩,
  begin
    intros a b H,
    dsimp,
    split_ifs with ha hb,
    { exact H },
    { simp at hb,
      have hb' : i.val ≤ nat.pred b.val :=
      begin
        rw ←nat.pred_succ i.val,
        exact nat.pred_le_pred hb
      end,
      exact nat.le_trans ha hb' },
    { exfalso,
      exact ha (nat.le_trans H h) },
    { exact nat.pred_le_pred H }
  end⟩

lemma simplicial_identity₁ {i j : [n+1]} (H : i ≤ j) : δ i ≫ δ j.succ = δ j ≫ δ i.cast_succ :=
begin
  rw simplex_category.hom_eq2,
  dsimp [category.comp, function.comp, δ],
  funext a,
  by_cases hja : (j.val ≤ a.val),
  { have hja' : ((fin.succ j).val ≤ (fin.succ a).val) := by simp; exact nat.succ_le_succ hja,
    have hia : ((fin.cast_succ i).val ≤ (fin.succ a).val) := by simp; exact nat.le_trans H (nat.le_trans hja (nat.le_succ a.val)),
    erw [dif_pos hja, dif_pos (nat.le_trans H hja), dif_pos hja', dif_pos hia] },
  { rw [dif_neg hja],
    by_cases hia : (i.val ≤ a.val),
    { have hia' : ((fin.cast_succ i).val ≤ (fin.cast_succ a).val) := hia,
      have hja' : ¬(j.succ.val ≤ a.succ.val) := by simp at *; exact nat.succ_le_succ hja,
      erw [dif_pos hia, dif_pos hia', dif_neg hja'],
      apply fin.eq_of_veq,
      simp },
    { have hja' : ¬(j.succ.val ≤ a.cast_succ.val) := by simp at *; exact nat.le_trans hja (nat.le_succ j.val),
      have hia' : ¬((fin.cast_succ i).val ≤ (fin.cast_succ a).val) := by unfold fin.cast_succ; exact hia,
      erw [dif_neg hia, dif_neg hja', dif_neg hia'] } }
end

-- lemma simplicial_identity₂ {i : [n+1]} {j : [n]} (H : i ≤ j.raise) : δ i.raise ≫ σ j.succ = σ j ≫ δ i := sorry
-- lemma simplicial_identity₃
-- lemma simplicial_identity₄
-- lemma simplicial_identity₅

end simplex_category
