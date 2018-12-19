import .pushout_lemmas

local attribute [instance] classical.prop_decidable

universe u

open category_theory set

namespace homotopy_theory.topological_spaces
open Top
local notation `Top` := Top.{u}

def closed_t1_inclusion {A X : Top} (i : A ⟶ X) : Prop :=
embedding i ∧ is_closed (set.range i) ∧ ∀ x, x ∉ set.range i → is_closed ({x} : set X)

lemma closed_t1_inclusion_of_closed_embedding_t1 {A X : Top} [t1_space X] (i : A ⟶ X)
  (h₁ : embedding i) (h₂ : is_closed (set.range i)) : closed_t1_inclusion i :=
⟨h₁, h₂, λ x _, is_closed_singleton⟩

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
       change (g'.inv ≫ g'.hom ≫ incl _).val ⟨y, hy⟩ = y,
       simp, refl },
     suffices : ∀ x', g x' = y → x' = x.val,
     { ext x',
       rw [mem_preimage_eq, mem_singleton_iff, mem_singleton_iff],
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
     exact congr_arg subtype.val ((homeomorphism.embedding g').1 this) },
   { convert is_closed_empty,
     rw ←preimage_inter_range,
     convert preimage_empty,
     rwa singleton_inter_eq_empty }
 end⟩

end

end homotopy_theory.topological_spaces
