import homotopy_theory.formal.cylinder.hep
import .category
import .colimits
import .cylinder
import .pushout_lemmas

open categories
open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

open homotopy_theory.cylinder

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{0}

-- The classical definition of a cofibration between topological
-- spaces as a map which satisfies the homotopy extension property.
def cofibration {A X : Top} (j : A ⟶ X) : Prop := hep 0 j

/-

* A cofibration in Top is an embedding. [Strøm, Note on cofibrations,
  Theorem 1.] Proof: Suppose j : A → X is a cofibration. Form the
  mapping cylinder Z as the pushout shown below, with induced map
  k : Z → IX.

      j
    A → X = X
  i₀↓   ↓   ↓i₀
   IA → Z → IX → Z
  i₁↑   ↑   ↑i₁
    A = A → X
          j

  By the homotopy extension property, we can find a map r from IX back
  to Z. So Z → X is the inclusion of a retract, hence in particular an
  embedding. The map i₀ : A → IA has closed image, so IA → Z is a
  homeomorphism onto its image away from the image of i₀. Thus the
  composition

      i₁
    A → IA → Z → IX

  is an embedding; but it equals i₁ ∘ j : A → IX, so j : A → X is an
  embedding as well.

-/

variables {A X : Top} {j : A ⟶ X}
local notation `i` := i.{1 0}

lemma embedding_i {ε} : embedding (i ε @> A) :=
embedding_of_embedding_comp (p @> A) embedding_id

lemma closed_i {ε} : is_closed (set.range (i ε @> A)) :=
have is_closed {p : Top.prod A I01 | p.snd ∈ ({I01_of_endpoint ε} : set I01)}, from
  continuous_iff_is_closed.mp continuous_snd _ is_closed_singleton,
begin
  convert this, ext p, cases p with a t,
  change (∃ a', (a', _) = (a, t)) ↔ _,
  simpa using eq_comm
end

lemma disjoint_i₀_i₁ : set.range (i 0 @> A) ∩ set.range (i 1 @> A) = ∅ :=
begin
  apply set.eq_empty_of_subset_empty, intros p hp,
  cases p with a t, rcases hp with ⟨⟨_, hp₀⟩, ⟨_, hp₁⟩⟩,
  cases prod.ext.mp hp₀ with _ hp₀', change 0 = t at hp₀',
  cases prod.ext.mp hp₁ with _ hp₁', change 1 = t at hp₁',
  have : (0 : I01) = 1 := hp₀'.trans hp₁'.symm,
  exact absurd (congr_arg subtype.val this)
    (show ¬(0 : ℝ) = 1, by norm_num)
end

lemma embedding_of_cofibration (h : cofibration j) : embedding j :=
let po := has_pushouts.pushout (i 0 @> A) j,
    Z := po.ob,
    k : Z ⟶ I +> X :=
      po.is_pushout.induced (I &> j) (i 0 @> X) ((i 0).naturality _).symm,
    ⟨r, hr₀, hr₁⟩ := h Z po.map₁ po.map₀ po.is_pushout.commutes.symm in
have _ := hr₀.symm,
have hr : r ∘ k = 1, by apply po.is_pushout.uniqueness; { rw ←associativity, simpa },
have e_z_ix : embedding k, from
  embedding_of_embedding_comp r (by rw hr; exact embedding_id),
have e_a_z : embedding (po.map₀ ∘ i 1 @> A), from
  comp_embedding_of_embedding_of_disjoint
    po.is_pushout (or.inl closed_i) embedding_i disjoint_i₀_i₁,
have embedding (k ∘ (po.map₀ ∘ i 1 @> A)), from
  embedding_compose e_a_z e_z_ix,
have embedding (i 1 @> X ∘ j), begin
  convert this using 2,
  transitivity,
  exact (i 1).naturality j,
  simp
end,
embedding_of_embedding_comp _ this

end homotopy_theory.topological_spaces
