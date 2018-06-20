import .homotopy_classes

universes u v

open categories

namespace homotopy_theory.cofibrations
-- Homotopy equivalences as the weak equivalences of an I-category.
open homotopy_theory.weak_equivalences

variables {C : Type u} [cat : category.{u v} C]
  [has_initial_object.{u v} C] [has_coproducts.{u v} C] [I_category.{u v} C]
include cat

instance homotopy_category.category_with_weak_equivalences :
  category_with_weak_equivalences (category_mod_congruence C homotopy_congruence) :=
isomorphisms_as_weak_equivalences

instance I_category.category_with_weak_equivalences : category_with_weak_equivalences C :=
preimage_with_weak_equivalences (quotient_functor C homotopy_congruence)

end homotopy_theory.cofibrations
