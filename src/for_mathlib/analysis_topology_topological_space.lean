import analysis.topology.topological_space

universes u v

open set

section
variables {α : Type u} [topological_space α]

lemma is_closed_diff {s t : set α} (h₁ : is_closed s) (h₂ : is_open t) : is_closed (s - t) :=
is_closed_inter h₁ $ is_closed_compl_iff.mpr h₂

end

section discrete
variables {α : Type u} {β : Type v}

lemma discrete_iff_all_open [t : topological_space α] :
  t = ⊤ ↔ ∀ (s : set α), is_open s :=
iff.intro
  (assume h s, by rw h; exact trivial)
  (assume h, topological_space_eq $ funext $ assume s,
    (@eq_true (is_open s)).symm ▸ h s)

lemma discrete_iff_singletons_open [t : topological_space α] :
  t = ⊤ ↔ ∀ x, is_open ({x} : set α) :=
discrete_iff_all_open.trans $ iff.intro
  (assume h x, h {x})
  (assume h s, have s = ⋃(x ∈ s), {x}, by ext; simp,
    by rw this; exact is_open_bUnion (assume x _, h x))

class discrete_space (α : Type u) :=
(to_topological_space : topological_space α := ⊤)
(is_discrete_topology : to_topological_space = ⊤ . control_laws_tac)

instance discrete_space.to_topological_space' [discrete_space α] : topological_space α :=
discrete_space.to_topological_space α

@[simp] lemma is_discrete_topology [t : discrete_space α] :
  @discrete_space.to_topological_space' α t = ⊤ := t.is_discrete_topology

@[simp] lemma is_open_of_discrete [t : discrete_space α] (s : set α) : is_open s :=
discrete_iff_all_open.mp t.is_discrete_topology s

@[simp] lemma is_closed_of_discrete [discrete_space α] (s : set α) : is_closed s :=
is_open_compl_iff.mpr $ is_open_of_discrete (-s)

instance : discrete_space empty := {}
instance : discrete_space unit := {}
instance : discrete_space bool := {}
instance : discrete_space ℕ := {}
instance : discrete_space ℤ := {}

instance {p : α → Prop} [discrete_space α] : discrete_space (subtype p) :=
{ to_topological_space := subtype.topological_space,
  is_discrete_topology := discrete_iff_all_open.mpr $ assume s,
    ⟨subtype.val '' s, is_open_of_discrete _,
     (preimage_image_eq _ $ assume a b h, subtype.eq h).symm⟩ }

/-
lemma is_open_prod [topological_space α] [topological_space β] {s : set α} {t : set β} (hs : is_open s) (ht : is_open t) :
  is_open (set.prod s t) :=
sorry

instance [discrete_space α] [discrete_space β] : discrete_space (α × β) :=
{ to_topological_space := prod.topological_space,
  is_discrete_topology := discrete_iff_singletons_open.mpr $ assume ⟨x, y⟩,
    by rw ←prod_singleton_singleton; apply is_open_prod; apply is_open_of_discrete }
-/

instance [discrete_space α] [discrete_space β] : discrete_space (α ⊕ β) :=
{ to_topological_space := sum.topological_space,
  is_discrete_topology := by unfold sum.topological_space; simp }

instance {β : α → Type v} [Πa, discrete_space (β a)] : discrete_space (sigma β) :=
{ to_topological_space := sigma.topological_space,
  is_discrete_topology := by unfold sigma.topological_space; simp }

end discrete

section compact
open filter
variables {α : Type u} [topological_space α]

lemma induced_nhds {s : set α} {x : α} (h : x ∈ s) :
  nhds (⟨x,h⟩ : subtype s) = vmap subtype.val (nhds x) :=
filter.ext.mpr $ assume r, by rw [mem_vmap_sets, nhds_sets, nhds_sets]; exact
  iff.intro
    (λ⟨t, tr, ⟨t', t'o, tt'⟩, xt⟩,
      ⟨t', ⟨t', subset.refl t', t'o, by subst tt'; exact xt⟩, tt' ▸ tr⟩)
    (λ⟨t, ⟨u, ut, uo, xu⟩, tr⟩,
      ⟨subtype.val ⁻¹' u, subset.trans (preimage_mono ut) tr, ⟨u, uo, rfl⟩, xu⟩)

-- TODO: Prove other direction using compact_image?
lemma compactness_intrinsic {s : set α} (s_cpt : compact s) :
  compact (univ : set (subtype s)) :=
begin
  rw compact_iff_ultrafilter_le_nhds at ⊢ s_cpt,
  intros f hf fs',
  let f' : filter α := map subtype.val f,
  have : f' ≤ principal s, begin
    rw [map_le_iff_le_vmap, vmap_principal], convert fs',
    apply ext, intro x, simpa using x.property,
  end,
  rcases s_cpt f' (ultrafilter_map hf) this with ⟨a, ha, h2⟩,
  refine ⟨⟨a, ha⟩, trivial, _⟩,
  rwa [induced_nhds, ←map_le_iff_le_vmap]
end

end compact
