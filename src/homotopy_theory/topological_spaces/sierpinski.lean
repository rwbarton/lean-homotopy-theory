import .category

namespace homotopy_theory.topological_spaces

open category_theory topological_space

--- The Sierpisnki space. It represents the (contravariant) functor
--- taking X to its set of open subsets.
def sierpinski : Top := Top.mk_ob (ulift Prop)

def opens_equiv (X : Top) : opens X ≃ (X ⟶ sierpinski) :=
⟨λ s, Top.mk_hom (λ x, ⟨x ∈ s.val⟩)
   (continuous.comp continuous_ulift_up (continuous_Prop.mpr s.property)),
 λ f, ⟨λ x, (f x).down, continuous_Prop.mp (by continuity)⟩,
 λ s, by ext; refl,
 λ f, by ext; refl⟩

lemma opens_equiv_nat {X Y : Top} (f : X ⟶ Y) (s : opens Y) :
  f ≫ opens_equiv Y s = opens_equiv X ⟨f ⁻¹' s, f.property s.val s.property⟩ :=
rfl

--- The two-point space with the indiscrete topology. It represents
--- the (contravariant) functor taking X to its set of all subsets.
def prop_indisc := @Top.mk_ob (ulift Prop) ⊤

def set_equiv (X : Top) : set X ≃ (X ⟶ prop_indisc) :=
⟨λ s, Top.mk_hom (λ x, ⟨x ∈ s⟩) (by continuity),
 λ f, λ x, (f x).down,
 λ s, by ext; refl,
 λ f, by ext; refl⟩

lemma set_equiv_nat {X Y : Top} (f : X ⟶ Y) (s : set Y) :
  f ≫ set_equiv Y s = set_equiv X (f ⁻¹' s) :=
rfl

def forget_open : sierpinski ⟶ prop_indisc := Top.mk_hom id

instance forget_open_mono : mono forget_open :=
⟨λ X f g h, by ext1; apply Top.hom_congr h⟩

lemma forget_open_map {X : Top} (s : opens X) :
  opens_equiv X s ≫ forget_open = set_equiv X s.val :=
rfl

end homotopy_theory.topological_spaces
