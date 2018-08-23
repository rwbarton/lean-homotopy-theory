--- Project-wide declarations related to category theory.

import category_theory.category
import tidy.tidy

-- Set up `tidy` as the tactic to be invoked by `obviously`.
@[obviously] meta def tidy_1 := tidy

-- `obviously` without trace
meta def obviously_ := tidy { tactics := default_tidy_tactics ++ obviously_tactics, trace_result := ff, trace_steps := ff }

-- TODO: Notation for composition of functors, etc.?

-- TODO: Transitional notation.
notation F ` &> `:85 f:85 := F.map f
