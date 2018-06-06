import .colimits

open set

open categories.category
local notation f ` ∘ `:80 g:80 := g ≫ f

universes u v

namespace categories

section

parameters {C : Type u} [cat : category.{u v} C]
include cat

parameters {a a' a'' : C} {f : a ⟶ a'} {g : a' ⟶ a''}
parameters {b b' b'' : C} {f' : b ⟶ b'} {g' : b' ⟶ b''}
parameters {i : a ⟶ b} {i' : a' ⟶ b'} {i'' : a'' ⟶ b''}

local notation a ` ~~ ` b := Bij_on _ a b

def Is_pushout_of_Is_pushout_of_Is_pushout
  (po : Is_pushout i f f' i') (po' : Is_pushout i' g g' i''):
  Is_pushout i (g ∘ f) (g' ∘ f') i'' :=
Is_pushout.mk $ λ x,
show Bij_on (λ (k : b'' ⟶ x), (k ∘ (g' ∘ f'), k ∘ i'')) univ {p | p.1 ∘ i = p.2 ∘ (g ∘ f)}, from
suffices Bij_on (λ (k : b'' ⟶ x), ((k ∘ g') ∘ f', k ∘ i'')) univ {p | p.1 ∘ i = (p.2 ∘ g) ∘ f}, by simpa,
calc univ ~~ {p : (b' ⟶ x) × (a'' ⟶ x) | p.1 ∘ i' = p.2 ∘ g}     : po'.universal x
     ...  ~~ {t : ((b ⟶ x) × (a' ⟶ x)) × (a'' ⟶ x) | _}          : Bij_on.restrict' (Bij_on.prod_right' (po.universal x)) {t | t.1.2 = t.2 ∘ g}
     ...  ~~ {t : ((b ⟶ x) × (a' ⟶ x)) × (a'' ⟶ x) | t.1.1 ∘ i = (t.2 ∘ g) ∘ f ∧ t.1.2 = t.2 ∘ g} :
  begin
    convert Bij_on.refl _, ext t,
    change
      t.1.1 ∘ i = (t.2 ∘ g) ∘ f ∧ t.1.2 = t.2 ∘ g ↔
      t.1.2 = t.2 ∘ g ∧ t.1.1 ∘ i = t.1.2 ∘ f ∧ true,
    simp, split; solve_by_elim { discharger := `[cc] }
  end
     ...  ~~ {p : (b ⟶ x) × (a'' ⟶ x) | p.1 ∘ i = (p.2 ∘ g) ∘ f} :
  show Bij_on (λ (t : (_ × _) × _), (t.1.1, t.2)) _ _, from
  -- Why can't we just use term mode here?
  begin
    fapply Bij_on.mk,
    exact {
      to_fun := λ t, ⟨(t.val.1.1, t.val.2), t.property.left⟩,
      inv_fun := λ p, ⟨((p.val.1, p.val.2 ∘ g), p.val.2), p.property, rfl⟩,
      left_inv := by intro t; rcases t with ⟨⟨⟨t₁₁, t₁₂⟩, t₂⟩, h⟩; tidy,
      right_inv := by intro p; rcases p with ⟨⟨p₁, p₂⟩, h⟩; refl },
    intro p, refl
  end

end

end categories
