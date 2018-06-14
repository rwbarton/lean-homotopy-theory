import analysis.topology.continuity

import .analysis_topology_locally_compact

open set

universes u v v'

variables (α : Type u) (β : Type v) [topological_space α] [topological_space β]

def continuous_map := {f : α → β // continuous f}
local notation `C(` α `,` β `)` := continuous_map α β

instance : has_coe_to_fun C(α, β) :=
{ F := λ _, α → β, coe := subtype.val }

variables {α β}

def compact_open_gen {s : set α} (hs : compact s) {u : set β} (hu : is_open u) :
  set C(α, β) :=
{f | f '' s ⊆ u}

local notation `M(` hs `,` hu `)` := compact_open_gen hs hu

-- The compact-open topology on the space continuous maps α → β.
def compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : compact s) (u : set β) (hu : is_open u), m = M(hs, hu)}

local attribute [instance] compact_open

lemma is_open_M {s : set α} (hs : compact s) {u : set β} (hu : is_open u) :
  is_open M(hs, hu) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

variables {β' : Type v'} [topological_space β']
variables {g : β → β'} (hg : continuous g)

def continuous_map.induced : C(α, β) → C(α, β') :=
λ f, ⟨g ∘ f, f.property.comp hg⟩

lemma preimage_M {s : set α} (hs : compact s) {u : set β'} (hu : is_open u) :
  continuous_map.induced hg ⁻¹' (M(hs, hu)) = M(hs, hg _ hu) :=
begin
  ext f, cases f with f _,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [image_comp, image_subset_iff]
end

lemma continuous_induced : continuous (continuous_map.induced hg : C(α, β) → C(α, β')) :=
continuous_generated_from $ assume m ⟨s, hs, u, hu, hm⟩,
  by rw [hm, preimage_M]; apply is_open_M

variables (α β)
def ev : C(α, β) × α → β := λ p, p.1 p.2
def coev : β → C(α, β × α) :=
λ b, ⟨λ a, (b, a), continuous.prod_mk continuous_const continuous_id⟩

variables {α β}
lemma continuous_ev [locally_compact_space α] : continuous (ev α β) :=
continuous_iff_tendsto.mpr $ assume ⟨⟨f, hf⟩, x⟩ n hn, 
  let ⟨v, vn, vo, fxv⟩ := mem_nhds_sets_iff.mp hn in
  have v ∈ (nhds (f x)).sets, from mem_nhds_sets vo fxv,
  let ⟨s, hs, sv, sc⟩ :=
    locally_compact_space.local_compact_nhds x (f ⁻¹' v) (hf.tendsto x this) in
  let ⟨u, us, uo, xu⟩ := mem_nhds_sets_iff.mp hs in
  show (ev α β) ⁻¹' n ∈ (nhds (⟨⟨f, hf⟩, x⟩ : C(α, β) × α)).sets, from
  let w := set.prod M(sc, vo) u in
  have w ⊆ ev α β ⁻¹' n, from assume ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f' x' ∈ f' '' s  : mem_image_of_mem f' (us hx')
    ...   ⊆ v        : hf'
    ...   ⊆ n        : vn,
  have is_open w, from is_open_prod (is_open_M _ _) uo,
  have (⟨⟨f, hf⟩, x⟩ : C(α, β) × α) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  mem_nhds_sets_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

lemma image_coev {y : β} (s : set α) : coev α β y '' s = set.prod {y} s := 
ext $ assume ⟨b, a⟩, calc
  (b, a) ∈ coev α β y '' s
    ↔ ∃ x, x ∈ s ∧ (y, x) = (b, a) : iff.rfl
... ↔ b = y ∧ a ∈ s                :
begin
  split,
  { intro h, rcases h with ⟨x, h1, h2⟩, split; cc },
  { intro h, rcases h with ⟨h1, h2⟩, existsi a, cc }
end
... ↔ (b, a) ∈ set.prod {y} s      : by rw ←mem_singleton_iff; refl

lemma continuous_coev : continuous (coev α β) :=
continuous_generated_from $ assume m ⟨s, sc, u, uo, hm⟩,
  is_open_iff_forall_mem_open.mpr $ assume y hy, begin
    let f := coev α β y,
    change f ∈ m at hy,
    rw hm at hy,
    change f '' s ⊆ u at hy,
    rw image_coev s at hy,
    rcases generalized_tube_lemma compact_singleton sc uo hy
      with ⟨v, w, vo, wo, yv, sw, vwu⟩,
    have : v ⊆ coev α β ⁻¹' m, from begin
      intros y' hy',
      rw hm,
      change coev α β y' '' s ⊆ u,
      rw image_coev s,
      exact calc
        set.prod {y'} s ⊆ set.prod v w  : prod_mono (singleton_subset_iff.mpr hy') sw
        ...             ⊆ u             : vwu
    end,
    exact ⟨v, this, vo, singleton_subset_iff.mp yv⟩
  end
