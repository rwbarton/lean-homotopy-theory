import category_theory.category
import data.equiv.basic -- for plift.subsingleton

universes u v

namespace category_theory

open plift ulift

instance {X : Type u} [partial_order X] : category.{u v} X :=
{ hom := λ x y, ulift $ plift (x ≤ y),
  id := λ x, up $ up (partial_order.le_refl x),
  comp := λ x y z f g, up $ up (partial_order.le_trans _ _ _ (down $ down f) (down $ down g)),
  id_comp := λ x y f, by rw ← ulift.up_down f; congr,
  comp_id := λ x y f, by rw ← ulift.up_down f; congr,
  assoc := λ w x y z f g h, by rw ← ulift.up_down f }

end category_theory
