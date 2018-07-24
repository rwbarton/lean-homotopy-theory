import categories.category

namespace categories

universes u v

class groupoid (Obj : Type u) extends category.{u v} Obj :=
  (inverse : Π {X Y : Obj}, Hom X Y → Hom Y X)
  (left_inverse : ∀ {X Y : Obj} (f : Hom X Y), compose (inverse f) f = 𝟙 Y . obviously)
  (right_inverse : ∀ {X Y : Obj} (f : Hom X Y), compose f (inverse f) = 𝟙 X . obviously)

notation f `⁻¹` := groupoid.inverse f

make_lemma groupoid.left_inverse
make_lemma groupoid.right_inverse

abbreviation large_groupoid (C : Type (u+1)) : Type (u+1) := groupoid.{u+1 u} C
abbreviation small_groupoid (C : Type u) : Type (u+1) := groupoid.{u u} C

end categories
