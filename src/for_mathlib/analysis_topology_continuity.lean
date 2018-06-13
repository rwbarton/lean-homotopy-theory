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

lemma embedding_inl {α β : Type*} [topological_space α] [topological_space β] : embedding (@sum.inl α β) :=
⟨λ _ _, sum.inl.inj_iff.mp,
  begin
    unfold sum.topological_space,
    apply le_antisymm,
    { intros u hu, existsi (@sum.inl α β '' u),
      change
        (is_open (@sum.inl α β ⁻¹' (@sum.inl α β '' u)) ∧
         is_open (@sum.inr α β ⁻¹' (@sum.inl α β '' u))) ∧
        u = sum.inl ⁻¹' (sum.inl '' u),
      rw [preimage_inl_image_inl, preimage_inr_image_inl],
      exact ⟨⟨hu, is_open_empty⟩, rfl⟩ },
    { rw induced_le_iff_le_coinduced, exact lattice.inf_le_left }
  end⟩

lemma embedding_inr {α β : Type*} [topological_space α] [topological_space β] : embedding (@sum.inr α β) :=
⟨λ _ _, sum.inr.inj_iff.mp,
  begin
    unfold sum.topological_space,
    apply le_antisymm,
    { intros u hu, existsi (@sum.inr α β '' u),
      change
        (is_open (@sum.inl α β ⁻¹' (@sum.inr α β '' u)) ∧
         is_open (@sum.inr α β ⁻¹' (@sum.inr α β '' u))) ∧
        u = sum.inr ⁻¹' (sum.inr '' u),
      rw [preimage_inl_image_inr, preimage_inr_image_inr],
      exact ⟨⟨is_open_empty, hu⟩, rfl⟩ },
    { rw induced_le_iff_le_coinduced, exact lattice.inf_le_right }
  end⟩
