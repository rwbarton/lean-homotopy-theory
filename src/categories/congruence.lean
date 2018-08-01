import categories.category
import categories.functor

universes u v

namespace categories
local notation f ` ∘ `:80 g:80 := g ≫ f

variables {C : Type u} [cat : category.{u v} C]
include cat

class congruence (r : Π ⦃a b : C⦄, (a ⟶ b) → (a ⟶ b) → Prop) :=
(is_equiv : ∀ {a b}, equivalence (@r a b))
(congr : ∀ {a b c} {f f' : a ⟶ b} {g g' : b ⟶ c}, r f f' → r g g' → r (g ∘ f) (g' ∘ f'))

def congruence.mk' {r : Π ⦃a b : C⦄, (a ⟶ b) → (a ⟶ b) → Prop}
  (is_equiv : ∀ {a b}, equivalence (@r a b))
  (congr_left : ∀ {a b c} {f f' : a ⟶ b} {g : b ⟶ c}, r f f' → r (g ∘ f) (g ∘ f'))
  (congr_right : ∀ {a b c} {f : a ⟶ b} {g g' : b ⟶ c}, r g g' → r (g ∘ f) (g' ∘ f)) :
  congruence r :=
{ is_equiv := @is_equiv,
  congr := λ _ _ _ f f' g g' rff' rgg',
    is_equiv.2.2 (congr_right rgg') (congr_left rff') }

variables (C)
variables (r : Π ⦃a b : C⦄, (a ⟶ b) → (a ⟶ b) → Prop) [congruence r]
include r
def category_mod_congruence : Type u := C
omit r

instance Hom.setoid (a b : C) : setoid (a ⟶ b) :=
{ r := @r a b, iseqv := congruence.is_equiv r }

instance : category (category_mod_congruence C r) :=
{ Hom := λ a b, quotient (Hom.setoid C r a b),
  identity := λ a, ⟦𝟙 a⟧,
  compose := λ a b c f₀ g₀, quotient.lift_on₂ f₀ g₀ (λ f g, ⟦g ∘ f⟧)
    (λ f g f' g' rff' rgg', quotient.sound (congruence.congr C rff' rgg' : r _ _)) }

def quotient_functor : C ↝ category_mod_congruence C r :=
{ onObjects := λ a, a, onMorphisms := λ a b f, ⟦f⟧ }

end categories
