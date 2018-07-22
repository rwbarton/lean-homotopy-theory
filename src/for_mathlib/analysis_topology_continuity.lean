import analysis.topology.continuity
import .data_sum

lemma continuous_of_embedding_of_continuous_comp {α β γ : Type*}
  [tα : topological_space α] [tβ : topological_space β] [tγ : topological_space γ]
  {f : α → β} {g : β → γ} (hg : embedding g) (hgf : continuous (g ∘ f)) :
  continuous f :=
continuous_iff_induced_le.mpr $
  by rw [hg.2, induced_compose]; exact continuous_iff_induced_le.mp hgf

lemma continuous_of_quotient_map_of_continuous_comp {α β γ : Type*}
  [tα : topological_space α] [tβ : topological_space β] [tγ : topological_space γ]
  {f : α → β} {g : β → γ} (hf : quotient_map f) (hgf : continuous (g ∘ f)) :
  continuous g :=
continuous_iff_le_coinduced.mpr $
  by rw [hf.2, coinduced_compose]; exact continuous_iff_le_coinduced.mp hgf
