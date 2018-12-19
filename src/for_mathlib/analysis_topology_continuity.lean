import analysis.topology.continuity

universes u v

section ulift

variables {α : Type u}

instance ulift.topological_space [t : topological_space α] : topological_space (ulift.{v u} α) :=
t.induced ulift.down

lemma continuous_down [topological_space α] : continuous (ulift.down : ulift.{v u} α → α) :=
continuous_induced_dom

lemma continuous_up [topological_space α] : continuous (ulift.up : α → ulift.{v u} α) :=
continuous_induced_rng continuous_id

end ulift


