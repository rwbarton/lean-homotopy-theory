import categories.category

universes u v

namespace categories

open plift ulift

instance {X : Type u} [partial_order X] : category.{u v} X :=
{ Hom := λ x y, ulift $ plift (x ≤ y),
  identity := λ x, up $ up (partial_order.le_refl x),
  compose := λ x y z f g, up $ up (partial_order.le_trans _ _ _ (down $ down f) (down $ down g)),
  left_identity := λ x y f, by rw ← ulift.up_down f; congr,
  right_identity := λ x y f, by rw ← ulift.up_down f; congr,
  associativity := λ w x y z f g h, by rw ← ulift.up_down f }

end categories