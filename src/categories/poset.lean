import categories.category

universes u

namespace categories

open plift

instance {X : Type u} [partial_order X] : category.{u} X :=
{ Hom := λ x y, plift (x ≤ y),
  identity := λ x, up (partial_order.le_refl x),
  compose := λ x y z f g, up (partial_order.le_trans _ _ _ (down f) (down g)),
  left_identity := λ x y f, up_down f,
  right_identity := λ x y f, up_down f,
  associativity := λ w x y z f g h, up_down _, }

end categories