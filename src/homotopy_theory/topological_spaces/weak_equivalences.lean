import homotopy_theory.formal.i_category.homotopy_equivalences
import .pi_n

open function

noncomputable theory

open category_theory (hiding is_iso)
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace homotopy_theory.topological_spaces
open homotopy_theory.cofibrations
open homotopy_theory.weak_equivalences
open homotopy_theory.topological_spaces.Top
local notation `Top` := Top.{0}
local notation `Set` := Type 0

def is_weak_equivalence {X Y : Top} (f : X ⟶ Y) : Prop :=
is_iso (π₀ &> f) ∧ ∀ n x, is_iso (π_induced n x f)

lemma is_weak_equivalence_iso {X Y : Top} (i : homeomorphism X Y) :
  is_weak_equivalence i.hom :=
⟨⟨π₀.map_iso i, rfl⟩,
 assume n x, ⟨(π n).map_iso (Top_ptd.mk_iso' i x), rfl⟩⟩

lemma is_weak_equivalence_comp {X Y Z : Top} {f : X ⟶ Y} {g : Y ⟶ Z}
  (hf : is_weak_equivalence f) (hg : is_weak_equivalence g) :
  is_weak_equivalence (g ∘ f) :=
⟨by rw π₀.map_comp; exact iso_comp hf.1 hg.1,
 assume n x, by rw π_induced_comp; exact iso_comp (hf.2 n x) (hg.2 n (f x))⟩

instance : replete_wide_subcategory.{1} Top @is_weak_equivalence :=
replete_wide_subcategory.mk' @is_weak_equivalence_iso @is_weak_equivalence_comp

-- I don't know why this changed, but `⟦Top.const y⟧` in the proof below
-- started using `subtype.setoid` and `fun_setoid` (from core) by default.
local attribute [instance, priority 1000] Hom.setoid

-- I don't know what this means, but lean told me to turn it on
set_option eqn_compiler.zeta true
def Top_weak_equivalences : category_with_weak_equivalences Top :=
{ is_weq := @is_weak_equivalence,
  weq_of_comp_weq_left := assume X Y Z f g hf hgf,
    ⟨iso_of_comp_iso_left hf.1 (by rw ←π₀.map_comp; exact hgf.1),
     assume n y,
     -- This is the nontrivial case: y may not be in the image of f.
     -- But we know that f is an isomorphism on π₀, so y is at least
     -- connected by a path to f x' for some x' : X.
       let ⟨i, hi⟩ := hf.1 in
       let x'_class := i.inv ⟦Top.const y⟧ in
       let ⟨x'_map, hx'⟩ := quotient.exists_rep x'_class in
       let x' := x'_map punit.star in
       have (π₀ &> f) ⟦Top.const x'⟧ = ⟦Top.const y⟧, from
         have Top.const x' = x'_map, by ext p; cases p; refl,
         begin
           rw [this, ←hi, hx'], dsimp [x'_class],
           change (i.hom ∘ i.inv) _ = _,
           erw i.inv_hom_id, refl
         end,
       have ⟦Top.const (f x')⟧ = ⟦Top.const y⟧, from this,
       let ⟨(γ : path (f x') y)⟩ := quotient.exact this in
       have is_iso (π_induced n (f x') g), from
         iso_of_comp_iso_left (hf.2 n x')
           (by rw ←π_induced_comp; exact hgf.2 n x'),
       let ⟨i', hi'⟩ := this in
       ⟨(change_of_basepoint n γ).symm.trans $
        i'.trans (change_of_basepoint n (γ.induced g)),
        show (change_of_basepoint n (γ.induced g)).hom ∘
            i'.hom ∘ (change_of_basepoint n γ).inv =
          π_induced n y g,
        by rw [hi', ←change_of_basepoint_induced, iso.inv_hom_id_assoc]⟩⟩,
  weq_of_comp_weq_right := assume X Y Z f g hg hgf,
    ⟨iso_of_comp_iso_right hg.1 (by rw ←π₀.map_comp; exact hgf.1),
     assume n x, iso_of_comp_iso_right (hg.2 n (f x))
       (by rw ←π_induced_comp; exact hgf.2 n x)⟩ }

lemma is_weak_equivalence_of_heq {X Y : Top} (f : X ⟶ Y)
  (h : homotopy_equivalence f) : is_weak_equivalence f :=
let ⟨g, gf1, fg1⟩ := homotopy_equivalence_iff.mp h in
⟨⟨⟨π₀ &> f, π₀ &> g,
   by rw [←π₀.map_comp, ←π₀.map_id]; exact π₀_induced_homotopic gf1,
   by rw [←π₀.map_comp, ←π₀.map_id]; exact π₀_induced_homotopic fg1⟩,
  rfl⟩,
 assume n x,
   have gf : _ := π_induced_homotopic_id n x gf1.symm,
   have fg : _ := π_induced_homotopic_id n (f x) fg1.symm,
   begin
     rw π_induced_comp at gf fg,
     letI : homotopical_category Set := isomorphisms_as_homotopical_category,
     change is_weq (π_induced n x f),
     exact weq_two_out_of_six_f fg gf
   end⟩

end homotopy_theory.topological_spaces
