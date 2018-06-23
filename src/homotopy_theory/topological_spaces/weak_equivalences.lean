import homotopy_theory.formal.weak_equivalences.definitions
import .pi_n

open function

noncomputable theory

open categories
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.weak_equivalences
open Top
local notation `Top` := Top.{0}
local notation `Set` := Type 0

def is_weak_equivalence {X Y : Top} (f : X ⟶ Y) : Prop :=
is_iso (π₀ &> f) ∧ ∀ n x, is_iso (π_induced n x f)

lemma is_weak_equivalence_iso {X Y : Top} (i : homeomorphism X Y) :
  is_weak_equivalence i.morphism :=
⟨⟨π₀.onIsomorphisms i, rfl⟩,
 assume n x, ⟨(π n).onIsomorphisms (Top_ptd.mk_iso' i x), rfl⟩⟩

lemma is_weak_equivalence_comp {X Y Z : Top} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : is_weak_equivalence f) (hg : is_weak_equivalence g) :
  is_weak_equivalence (g ∘ f) :=
⟨by rw π₀.functoriality; exact iso_comp hf.1 hg.1,
 assume n x, by rw π_induced_comp; exact iso_comp (hf.2 n x) (hg.2 n (f x))⟩

instance : replete_wide_subcategory.{1 0} Top @is_weak_equivalence :=
replete_wide_subcategory.mk' @is_weak_equivalence_iso @is_weak_equivalence_comp

-- I don't know what this means, but lean told me to turn it on
set_option eqn_compiler.zeta true
def Top_weak_equivalences : category_with_weak_equivalences Top :=
{ is_weq := @is_weak_equivalence,
  weq_of_comp_weq_left := assume X Y Z f g hf hgf,
    ⟨iso_of_comp_iso_left hf.1 (by rw ←π₀.functoriality; exact hgf.1),
     assume n y,
     -- This is the nontrivial case: y may not be in the image of f.
     -- But we know that f is an isomorphism on π₀, so y is at least
     -- connected by a path to f x' for some x' : X.
       let ⟨i, hi⟩ := hf.1 in
       let x'_class := i.inverse ⟦Top.const y⟧ in
       let ⟨x'_map, hx'⟩ := quotient.exists_rep x'_class in
       let x' := x'_map punit.star in
       have (π₀ &> f) ⟦Top.const x'⟧ = ⟦Top.const y⟧, from
         have Top.const x' = x'_map, by ext p; cases p; refl,
         begin
           rw [this, ←hi, hx'], dsimp [x'_class],
           change (i.morphism ∘ i.inverse) _ = _,
           rw i.witness_2_lemma, refl
         end,
       have ⟦Top.const (f x')⟧ = ⟦Top.const y⟧, from this,
       let ⟨(γ : path (f x') y)⟩ := quotient.exact this in
       have is_iso (π_induced n (f x') g), from
         iso_of_comp_iso_left (hf.2 n x')
           (by rw ←π_induced_comp; exact hgf.2 n x'),
       let ⟨i', hi'⟩ := this in
       ⟨(change_of_basepoint n γ).symm.trans $
        i'.trans (change_of_basepoint n (γ.induced g)),
        show (change_of_basepoint n (γ.induced g)).morphism ∘
            i'.morphism ∘ (change_of_basepoint n γ).inverse =
          π_induced n y g, from
        begin rw [hi'], rw ←change_of_basepoint_induced, simp end⟩⟩,
  weq_of_comp_weq_right := assume X Y Z f g hg hgf,
    ⟨iso_of_comp_iso_right hg.1 (by rw ←π₀.functoriality; exact hgf.1),
     assume n x, iso_of_comp_iso_right (hg.2 n (f x))
       (by rw ←π_induced_comp; exact hgf.2 n x)⟩ }

end homotopy_theory.topological_spaces
