import analysis.topology.continuity

import .analysis_topology_topological_space
import .data_set_basic

open set

universe u

-- There are various definitions of "locally compact space" in the
-- literature, which agree for Hausdorff spaces. We have chosen this
-- one because it is what is needed for the compact-open topology on
-- spaces of continuous maps with locally compact domain to have the
-- expected properties (namely, to be an exponential object in Top).
class locally_compact_space (α : Type u) [topological_space α] :=
(local_compact_nhds :
  ∀ (x : α) (n ∈ (nhds x).sets), ∃ s ∈ (nhds x).sets, s ⊆ n ∧ compact s)

variables {α : Type u} [topological_space α]

-- TODO: compact_diff?
lemma locally_compact_of_compact_nhds [t2_space α]
  (h : ∀ x : α, ∃ s, s ∈ (nhds x).sets ∧ compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_sets_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
    compact_compact_separated
      compact_singleton
      (compact_of_is_closed_subset kc
        (is_closed_diff (closed_of_compact k kc) uo)
        (inter_subset_left _ _))
      (by rw [singleton_inter_eq_empty]; exact λ h, h.2 xu) in
  have wn : -w ∈ (nhds x).sets, from
   mem_nhds_sets_iff.mpr
     ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩,
  ⟨k - w,
   filter.inter_mem_sets kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   compact_of_is_closed_subset kc
     (is_closed_diff (closed_of_compact k kc) wo)
     (inter_subset_left _ _)⟩⟩

lemma locally_compact_of_compact [t2_space α] (h : compact (univ : set α)) :
  locally_compact_space α :=
locally_compact_of_compact_nhds
  (assume x, ⟨univ, mem_nhds_sets is_open_univ trivial, h⟩)
