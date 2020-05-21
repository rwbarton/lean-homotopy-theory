import topology.algebra.ring
import tactic.tidy
import for_mathlib.tidy

attribute [back]
  continuous_id
  continuous_subtype_val
  continuous_fst continuous_snd
  continuous_inl continuous_inr continuous_sum_rec
  continuous_top continuous_bot
  continuous_ulift_up continuous_ulift_down

-- Applying continuous.comp is not always a good idea, so we have some
-- extra logic here to try to avoid bad cases.
--
-- * If the function we're trying to prove is actually constant, and
-- that constant is a function application `f z`, then continuous.comp
-- would produce new goals `continuous f`, `continuous (λ _, z)`,
-- which is silly. We avoid this by failing if we could apply
-- continuous_const.
--
-- * continuous.comp will always succeed on `continuous (λ x, f x)`
-- and produce new goals `continuous (λ x, x)`, `continuous f`. We
-- detect this by failing if a new goal can be closed by applying
-- continuous_id.
@[tidy] meta def apply_continuous.comp :=
`[fail_if_success { exact continuous_const };
  refine continuous.comp _ _;
  fail_if_success { exact continuous_id }]

-- `apply` is often not smart enough to guess how many auxiliary goals
-- to add when that number is not 1. We add tidy tactics with the
-- correct number of goals specified explicitly.
@[tidy] meta def apply_continuous_subtype_mk := `[refine continuous_subtype_mk _ _]
@[tidy] meta def apply_continuous.prod_mk := `[refine continuous.prod_mk _ _]
@[tidy] meta def apply_continuous_min := `[refine continuous.min _ _]
@[tidy] meta def apply_continuous_max := `[refine continuous.max _ _]
@[tidy] meta def apply_continuous_neg' := `[exact continuous_neg]
@[tidy] meta def apply_continuous_add := `[refine continuous.add _ _]
@[tidy] meta def apply_continuous_sub := `[refine continuous.sub _ _]
@[tidy] meta def apply_continuous_mul := `[refine continuous.mul _ _]
@[tidy] meta def apply_continuous_const := `[exact continuous_const]

open tactic

meta def continuity_tactics : list (tactic string) :=
[
  backwards_reasoning,
  auto_cases,
  tactic.interactive.apply_assumption    >> pure "apply_assumption",
  tidy.run_tactics
]

meta def continuity (cfg : tidy.cfg := {}) : tactic unit :=
let cfg' := { tactics := continuity_tactics, ..cfg } in
tidy cfg'

-- For use with auto_param
meta def continuity' : tactic unit := continuity
