import .pushout_lemmas

local attribute [instance] classical.prop_decidable

universe u

open category_theory set

namespace homotopy_theory.topological_spaces
open homotopy_theory.topological_spaces.Top
local notation `Top` := Top.{u}

def closed_t1_inclusion {A X : Top} (i : A ⟶ X) : Prop :=
embedding i ∧ is_closed (set.range i) ∧ ∀ x, x ∉ set.range i → is_closed ({x} : set X)

lemma closed_t1_inclusion_of_closed_embedding_t1 {A X : Top} [t1_space X] (i : A ⟶ X)
  (h₁ : embedding i) (h₂ : is_closed (set.range i)) : closed_t1_inclusion i :=
⟨h₁, h₂, λ x _, is_closed_singleton⟩

lemma closed_t1_inclusion_id {X : Top} : closed_t1_inclusion (𝟙 X) :=
⟨embedding_id, by convert is_closed_univ; exact range_id, λ x hx, false.elim (hx ⟨x, rfl⟩)⟩

lemma closed_t1_inclusion_comp {X Y Z : Top} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : closed_t1_inclusion f) (hg : closed_t1_inclusion g) : closed_t1_inclusion (f ≫ g) :=
⟨hg.1.comp hf.1,
 by convert embedding_is_closed hg.1 hg.2.1 hf.2.1; apply range_comp,
 λ z hz, if hz' : z ∈ range g
   then let ⟨y, hy⟩ := hz' in
     have y ∉ range f, from λ hy', hz (by erw range_comp; exact ⟨y, hy', hy⟩),
     by convert embedding_is_closed hg.1 hg.2.1 (hf.2.2 y this); rw ←hy; simp
   else hg.2.2 z hz'⟩

section
parameters {A B X Y : Top} {i : A ⟶ X} {f : A ⟶ B} {g : X ⟶ Y} {j : B ⟶ Y}
parameter (po : Is_pushout i f g j)
include po

lemma closed_t1_inclusion_of_pushout (h : closed_t1_inclusion i) : closed_t1_inclusion j :=
⟨embedding_j_of_embedding_i po h.1,
 (range_i_closed_iff_range_j_closed po).mp h.2.1,
 λ y hy, begin
   rw is_closed_in_pushout po, split,
   { let g' := complement_homeomorphism po (or.inl h.2.1),
     let x := g'.inv ⟨y, hy⟩,
     suffices : g ⁻¹' {y} = {x.val},
     { rw this, apply h.2.2 x.val x.property },
     have g'x : g'.hom x = ⟨y, hy⟩,
     { ext,
       change (g'.inv ≫ g'.hom ≫ incl _) ⟨y, hy⟩ = y,
       simp, refl },
     suffices : ∀ x', g x' = y → x' = x.val,
     { ext x',
       rw [mem_preimage, mem_singleton_iff, mem_singleton_iff],
       refine ⟨this x', _⟩,
       rintro rfl,
       convert Top.hom_congr (complement_homeomorphism_eq po (or.inl h.2.1)).symm x,
       exact congr_arg subtype.val g'x.symm },
     intros x' hx',
     have : x' ∉ range i,
     { rintro ⟨a, rfl⟩,
       change (i ≫ g) a = y at hx',
       rw po.commutes at hx',
       exact hy ⟨f a, hx'⟩ },
     have : g'.hom ⟨x', this⟩ = ⟨y, hy⟩,
     { ext,
       convert ←Top.hom_congr (complement_homeomorphism_eq po (or.inl h.2.1)).symm ⟨x', this⟩ },
     have : g'.hom ⟨x', _⟩ = g'.hom x, from this.trans g'x.symm,
     exact congr_arg subtype.val ((homeomorphism.embedding g').inj this) },
   { convert is_closed_empty,
     rw ←preimage_inter_range,
     convert preimage_empty,
     -- FIXME: Used to be `rwa singleton_inter_eq_empty`
     exact singleton_inter_eq_empty.mpr hy }
 end⟩

end

end homotopy_theory.topological_spaces
