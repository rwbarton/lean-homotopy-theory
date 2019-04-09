import category_theory.category
import data.is_equiv
import data.bij_on

/-

The basic finite colimit notions: initial objects, (binary)
coproducts, coequalizers and pushouts.

For each notion X, we define three structures/classes:

* `Is_X`, parameterized by a cocone diagram (but not on the
  commutativity condition!), which describes the commutativity and the
  universal property of the cocone. For example, a value of type
  `Is_pushout f₀ f₁ g₀ g₁` represents the property that the square
  formed by the four morphisms commutes and is a pushout square.

  Each `Is_X` is a subsingleton, but not a Prop, because we want to be
  able to constructively obtain the morphisms whose existence is
  guaranteed by the universal property.

* `X`, parameterized by the "input diagram" for the corresponding sort
  of colimit, which contains the data of a colimit of that sort on
  that diagram. For example, `pushout f₀ f₁` consists of an object and
  two maps which form a pushout square together with the given maps f₀
  and f₁. These structures are not subsingletons, because colimits are
  unique only up to unique isomorphism. This structure exists mostly
  to be used in the corresponding `has_X` class.

* `has_X`, a class for categories, which contains the data of a choice
  of `X` for each possible "input diagram". Thus an instance of
  `has_pushouts` is a category with a specified choice of pushout
  cocone on each span. It is not a subsingleton for the same reason
  that `X` is not one.

The `has_X` classes are of obvious importance, but the `Is_X`
structures are also very useful, especially in settings where colimits
of type X are not known to exist a priori. For example, preservation
of colimits by functors (in the usual "up to isomorphism" sense, not
strictly preserving the chosen colimits) is naturally formulated in
terms of `Is_X`, as is the standard fact about gluing together pushout
squares.

We define the `Is_X` structures by directly encoding the universal
property using the `Is_equiv` type, a constructive version of
`bijective`. Not sure yet whether this has advantages. In any case we
provide an alternate "first-order" interface through `mk'`
constructors and lemmas.

-/

-- TODO: "first-order" lemmas for the other notions besides coequalizers

open category_theory.category
local notation f ` ∘ `:80 g:80 := g ≫ f

namespace category_theory
section

universes v u
parameters {C : Type u} [cat : category.{v+1} C]
include cat


section initial_object

section Is
-- The putative initial object.
parameters {a : C}

-- An object is initial if for each x, the Hom set `a ⟶ x` is a
-- singleton.
def initial_object_comparison (x : C) : (a ⟶ x) → true :=
λ _, trivial

parameters (a)
-- The (constructive) property of being an initial object.
structure Is_initial_object : Type (max u v) :=
(universal : Π x, Is_equiv (initial_object_comparison x))

instance Is_initial_object.subsingleton : subsingleton Is_initial_object :=
⟨by intros p p'; cases p; cases p'; congr⟩

parameters {a}
-- Alternative verification of being an initial object.
def Is_initial_object.mk'
  (induced : Π {x}, a ⟶ x)
  (uniqueness : ∀ {x} (k k' : a ⟶ x), k = k') :
  Is_initial_object :=
{ universal := λ x,
  { e :=
    { to_fun := initial_object_comparison x,
      inv_fun := λ p, induced,
      left_inv := assume h, uniqueness _ _,
      right_inv := assume p, rfl },
    h := rfl } }

parameters (H : Is_initial_object)
def Is_initial_object.induced {x} : a ⟶ x :=
(H.universal x).e.symm trivial

def Is_initial_object.uniqueness {x} (k k' : a ⟶ x) : k = k' :=
(H.universal x).bijective.1 rfl

end Is

-- An initial object.
structure initial_object :=
(ob : C)
(is_initial_object : Is_initial_object ob)

parameters (C)
-- A choice of initial object. (This is basically the same as
-- initial_object, since there are no "parameters" in the definition
-- of an initial object.)
class has_initial_object :=
(initial_object : initial_object)

end initial_object


section coproduct

section Is
-- The putative coproduct diagram.
parameters {a₀ a₁ b : C} {f₀ : a₀ ⟶ b} {f₁ : a₁ ⟶ b}

-- The diagram above is a coproduct diagram when giving a map b ⟶ x is
-- the same as giving a map a₀ ⟶ x and a map a₁ ⟶ x.
def coproduct_comparison (x : C) : (b ⟶ x) → (a₀ ⟶ x) × (a₁ ⟶ x) :=
λ k, (k ∘ f₀, k ∘ f₁)

parameters (f₀ f₁)
-- The (constructive) property of being a coproduct.
structure Is_coproduct : Type (max u v) :=
(universal : Π x, Is_equiv (coproduct_comparison x))

instance Is_coproduct.subsingleton : subsingleton Is_coproduct :=
⟨by intros p p'; cases p; cases p'; congr⟩

parameters {f₀ f₁}
-- Alternative verification of being a coproduct.
def Is_coproduct.mk'
  (induced : Π {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x), b ⟶ x)
  (induced_commutes₀ : ∀ {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x), induced h₀ h₁ ∘ f₀ = h₀)
  (induced_commutes₁ : ∀ {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x), induced h₀ h₁ ∘ f₁ = h₁)
  (uniqueness : ∀ {x} (k k' : b ⟶ x), k ∘ f₀ = k' ∘ f₀ → k ∘ f₁ = k' ∘ f₁ → k = k') :
  Is_coproduct :=
{ universal := λ x,
  { e :=
    { to_fun := coproduct_comparison x,
      inv_fun := λ p, induced p.1 p.2,
      left_inv := assume h, by
        apply uniqueness; rw induced_commutes₀ <|> rw induced_commutes₁; refl,
      right_inv := assume p, prod.ext
        (induced_commutes₀ p.1 p.2)
        (induced_commutes₁ p.1 p.2) },
    h := rfl } }

parameters (H : Is_coproduct)
def Is_coproduct.induced {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x) : b ⟶ x :=
(H.universal x).e.inv_fun (h₀, h₁)

@[simp] lemma Is_coproduct.induced_commutes₀ {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x) :
  H.induced h₀ h₁ ∘ f₀ = h₀ :=
congr_arg prod.fst (H.universal x).cancel_right

@[simp] lemma Is_coproduct.induced_commutes₁ {x} (h₀ : a₀ ⟶ x) (h₁ : a₁ ⟶ x) :
  H.induced h₀ h₁ ∘ f₁ = h₁ :=
congr_arg prod.snd (H.universal x).cancel_right

lemma Is_coproduct.uniqueness {x : C} {k k' : b ⟶ x}
  (e₀ : k ∘ f₀ = k' ∘ f₀) (e₁ : k ∘ f₁ = k' ∘ f₁) : k = k' :=
(H.universal x).bijective.1 (prod.ext e₀ e₁)

end Is

-- A coproduct of a given diagram.
structure coproduct (a₀ a₁ : C) :=
(ob : C)
(map₀ : a₀ ⟶ ob)
(map₁ : a₁ ⟶ ob)
(is_coproduct : Is_coproduct map₀ map₁)

parameters (C)
-- A choice of coproducts of all diagrams.
class has_coproducts :=
(coproduct : Π (a₀ a₁ : C), coproduct a₀ a₁)

end coproduct


section coequalizer

section Is
-- The putative coequalizer diagram. `commutes` is a `variable`
-- because we do not want to index `Is_coequalizer` on it.
parameters {a b c : C} {f₀ f₁ : a ⟶ b} {g : b ⟶ c}
variables (commutes : g ∘ f₀ = g ∘ f₁)

-- The diagram above is a coequalizer diagram when giving a map c ⟶ x
-- is the same as giving a map b ⟶ x whose two pullback to a ⟶ x
-- agree.
def coequalizer_comparison (x : C) : (c ⟶ x) → {h : b ⟶ x // h ∘ f₀ = h ∘ f₁} :=
λ k, ⟨k ∘ g, have _ := commutes, by rw [←assoc, ←assoc, this]⟩

parameters (f₀ f₁ g)
-- The (constructive) property of being a coequalizer diagram.
-- TODO: Rewrite this in the same way as Is_pushout, using Bij_on?
structure Is_coequalizer : Type (max u v) :=
(commutes : g ∘ f₀ = g ∘ f₁)
(universal : Π x, Is_equiv (coequalizer_comparison commutes x))

instance Is_coequalizer.subsingleton : subsingleton Is_coequalizer :=
⟨by intros p p'; cases p; cases p'; congr⟩

parameters {f₀ f₁ g}
-- Alternative verification of being a coequalizer.
def Is_coequalizer.mk'
  (induced : Π {x} (h : b ⟶ x), h ∘ f₀ = h ∘ f₁ → (c ⟶ x))
  (induced_commutes : ∀ {x} (h : b ⟶ x) (e), induced h e ∘ g = h)
  (uniqueness : ∀ {x} (k k' : c ⟶ x), k ∘ g = k' ∘ g → k = k') :
  Is_coequalizer :=
{ commutes := commutes,
  universal := λ x,
  { e :=
    { to_fun := coequalizer_comparison commutes x,
      inv_fun := λ p, induced p.val p.property,
      left_inv := assume h, by apply uniqueness; rw induced_commutes; refl,
      right_inv := assume p, subtype.eq (induced_commutes p.val p.property) },
    h := rfl } }

parameters (H : Is_coequalizer)
def Is_coequalizer.induced {x} (h : b ⟶ x) (e : h ∘ f₀ = h ∘ f₁) : c ⟶ x :=
(H.universal x).e.symm ⟨h, e⟩

@[simp] lemma Is_coequalizer.induced_commutes {x} (h : b ⟶ x) (e) :
  H.induced h e ∘ g = h :=
congr_arg subtype.val $ (H.universal x).cancel_right

lemma Is_coequalizer.uniqueness {x} {k k' : c ⟶ x} (e : k ∘ g = k' ∘ g) : k = k' :=
(H.universal x).bijective.1 (subtype.eq e)

end Is

-- A coequalizer of a given diagram.
structure coequalizer {a b : C} (f₀ f₁ : a ⟶ b) :=
(ob : C)
(map : b ⟶ ob)
(is_coequalizer : Is_coequalizer f₀ f₁ map)

parameters (C)
-- A choice of coequalizers of all diagrams.
class has_coequalizers :=
(coequalizer : Π ⦃a b : C⦄ (f₀ f₁ : a ⟶ b), coequalizer f₀ f₁)

end coequalizer


section pushout

section Is
-- The putative pushout diagram.
-- TODO: Order of indices? I sometimes prefer the "f g f' g' order",
-- where f' is the pushout of f and g' is the pushout of g; that's
-- "f₀ f₁ g₁ g₀" here.
parameters {a b₀ b₁ c : C} {f₀ : a ⟶ b₀} {f₁ : a ⟶ b₁} {g₀ : b₀ ⟶ c} {g₁ : b₁ ⟶ c}

-- The diagram above is a pushout diagram when giving a map c ⟶ x is
-- the same as giving a map b₀ ⟶ x and a map b₁ ⟶ x whose pullbacks to
-- a ⟶ x agree.
def pushout_comparison (commutes : g₀ ∘ f₀ = g₁ ∘ f₁) (x : C) :
  (c ⟶ x) → {p : (b₀ ⟶ x) × (b₁ ⟶ x) // p.1 ∘ f₀ = p.2 ∘ f₁} :=
λ k, ⟨(k ∘ g₀, k ∘ g₁), have _ := commutes, by rw [←assoc, ←assoc, this]⟩

parameters (f₀ f₁ g₀ g₁)
-- The (constructive) property of being a pushout.
structure Is_pushout : Type (max u v) :=
(universal : Π x,
  Bij_on (λ (k : c ⟶ x), (k ∘ g₀, k ∘ g₁)) set.univ {p | p.1 ∘ f₀ = p.2 ∘ f₁})

instance Is_pushout.subsingleton : subsingleton Is_pushout :=
⟨by intros p p'; cases p; cases p'; congr⟩

parameters {f₀ f₁ g₀ g₁}
-- Alternative verification of being a pushout.
def Is_pushout.mk'
  (commutes : g₀ ∘ f₀ = g₁ ∘ f₁)
  (induced : Π {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x), h₀ ∘ f₀ = h₁ ∘ f₁ → (c ⟶ x))
  (induced_commutes₀ : ∀ {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e), induced h₀ h₁ e ∘ g₀ = h₀)
  (induced_commutes₁ : ∀ {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e), induced h₀ h₁ e ∘ g₁ = h₁)
  (uniqueness : ∀ {x} (k k' : c ⟶ x), k ∘ g₀ = k' ∘ g₀ → k ∘ g₁ = k' ∘ g₁ → k = k') :
  Is_pushout :=
{ universal := λ x,
  Bij_on.mk_univ
    { to_fun := pushout_comparison commutes x,
      inv_fun := λ p, induced p.val.1 p.val.2 p.property,
      left_inv := assume h, by
        apply uniqueness; rw induced_commutes₀ <|> rw induced_commutes₁; refl,
      right_inv := assume p, subtype.eq $ prod.ext
        (induced_commutes₀ p.val.1 p.val.2 p.property)
        (induced_commutes₁ p.val.1 p.val.2 p.property) }
    (assume p, rfl) }

parameters (H : Is_pushout)
include H

def Is_pushout.commutes : g₀ ∘ f₀ = g₁ ∘ f₁ :=
by convert (H.universal c).maps_to (_ : 𝟙 c ∈ set.univ); simp

def Is_pushout.induced {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e : h₀ ∘ f₀ = h₁ ∘ f₁) : c ⟶ x :=
(H.universal x).e.symm ⟨(h₀, h₁), e⟩

private lemma Is_pushout.induced_commutes' {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e) :
  (λ (k : c ⟶ x), (k ∘ g₀, k ∘ g₁)) (H.induced h₀ h₁ e) = (h₀, h₁) :=
(H.universal x).right_inv ⟨(h₀, h₁), e⟩

@[simp] lemma Is_pushout.induced_commutes₀ {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e) :
  H.induced h₀ h₁ e ∘ g₀ = h₀ :=
congr_arg prod.fst (Is_pushout.induced_commutes' h₀ h₁ e)

@[simp] lemma Is_pushout.induced_commutes₁ {x} (h₀ : b₀ ⟶ x) (h₁ : b₁ ⟶ x) (e) :
  H.induced h₀ h₁ e ∘ g₁ = h₁ :=
congr_arg prod.snd (Is_pushout.induced_commutes' h₀ h₁ e)

lemma Is_pushout.uniqueness {x} {k k' : c ⟶ x}
  (e₀ : k ∘ g₀ = k' ∘ g₀) (e₁ : k ∘ g₁ = k' ∘ g₁) : k = k' :=
(H.universal x).injective (prod.ext e₀ e₁)

end Is

-- A pushout of a given diagram.
structure pushout {a b₀ b₁ : C} (f₀ : a ⟶ b₀) (f₁ : a ⟶ b₁) :=
(ob : C)
(map₀ : b₀ ⟶ ob)
(map₁ : b₁ ⟶ ob)
(is_pushout : Is_pushout f₀ f₁ map₀ map₁)

parameters (C)
-- A choice of pushouts of all diagrams.
class has_pushouts :=
(pushout : Π ⦃a b₀ b₁ : C⦄ (f₀ : a ⟶ b₀) (f₁ : a ⟶ b₁), pushout f₀ f₁)

end pushout


end
end category_theory
