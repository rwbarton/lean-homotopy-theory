import topology.algebra.ordered
import topology.algebra.ring
import tactic.tidy
import for_mathlib.tidy

open tactic

@[user_attribute]
meta def continuity_attr : user_attribute :=
{ name := `continuity,
  descr := "lemmas usable to prove continuity" }

attribute [continuity]
  continuous_id
  continuous_subtype_val
  continuous_fst continuous_snd
  continuous_inl continuous_inr continuous_sum_rec
  continuous_top continuous_bot
  continuous_ulift_up continuous_ulift_down
  continuous_subtype_mk
  continuous_quot_mk continuous_quot_lift
  continuous.prod_mk
  continuous.min continuous.max
  continuous_neg
  continuous.add continuous.sub continuous.mul
  continuous_const

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
meta def apply_continuous.comp : tactic unit :=
`[fail_if_success { exact continuous_const };
  refine continuous.comp _ _;
  fail_if_success { exact continuous_id }]

meta def continuity_tactics : list (tactic string) :=
[
  `[apply_rules continuity]            >> pure "apply_rules continuity",
  auto_cases,
  tactic.interactive.apply_assumption  >> pure "apply_assumption",
  apply_continuous.comp                >> pure "refine continuous.comp _ _"
]

meta def continuity (cfg : tidy.cfg := {}) : tactic unit :=
let cfg' := { tactics := continuity_tactics, ..cfg } in do
  set_basic_attribute `irreducible `continuous,
  tidy cfg',
  set_basic_attribute `semireducible `continuous

-- For use with auto_param
meta def continuity' : tactic unit := continuity
