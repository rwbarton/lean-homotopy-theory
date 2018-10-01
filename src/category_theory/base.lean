--- Project-wide declarations related to category theory.

import category_theory.functor
import tactic.tidy

-- Set up `tidy` as the tactic to be invoked by `obviously`.
@[obviously] meta def tidy_1 := tactic.interactive.tidy

-- TODO: Notation for composition of functors, etc.?

-- TODO: Transitional notation.
notation F ` &> `:85 f:85 := F.map f
infixr ` ↝ `:80 := category_theory.functor
