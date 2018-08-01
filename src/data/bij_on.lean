import data.equiv
import data.set.function
import for_mathlib

import data.is_equiv

open set equiv

section Bij_on

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

-- A constructive version of bij_on: f : a → b is an equivalence. Note
-- that f is defined on all of α, but its inverse need only be defined
-- on b ⊆ β.
structure Bij_on (f : α → β) (a : set α) (b : set β) :=
(e : a ≃ b)
(he : ∀ (x : a), f x = e x)

variables {f : α → β} {a : set α} {b : set β}

-- Alternate constructor for the case when a = univ.
def Bij_on.mk_univ (e : α ≃ b) (he : ∀ x, f x = e x) : Bij_on f univ b :=
{ e := (equiv.set.univ _).trans e,
  he := assume x, by rw [he x]; refl }

-- Construct a bijection from an equivalence.
def Bij_on.of_equiv (e : α ≃ β) : Bij_on e.to_fun univ univ :=
Bij_on.mk_univ (e.trans (equiv.set.univ _).symm) (by intro x; refl)

def Bij_on.of_Is_equiv (h : Is_equiv f) : Bij_on f univ univ :=
by convert Bij_on.of_equiv h.e; funext a; rw [h.h] { occs := occurrences.pos [1] }; refl

def Bij_on.Is_equiv (h : Bij_on f univ univ) : Is_equiv f :=
{ e := (equiv.set.univ _).symm.trans (h.e.trans (equiv.set.univ _)),
  h := funext $ λ a, h.he ⟨a, trivial⟩ }

lemma Bij_on.he' (h : Bij_on f a b) {x : α} (hx : x ∈ a) : f x = h.e ⟨x, hx⟩ :=
h.he ⟨x, hx⟩

instance (f : α → β) (a : set α) (b : set β) :
  subsingleton (Bij_on f a b) :=
⟨assume ⟨e, he⟩ ⟨e', he'⟩,
 have e = e', from eq_of_to_fun_eq
   (by funext x; apply subtype.eq; exact (he x).symm.trans (he' x)),
 by cc⟩

lemma Bij_on.maps_to (h : Bij_on f a b) : maps_to f a b :=
assume x hx, show f x ∈ b, by rw h.he' hx; exact (h.e _).property

lemma Bij_on.inj_on (h : Bij_on f a b) : inj_on f a :=
assume x x' hx hx' hh, begin
  rw [h.he' hx, h.he' hx'] at hh,
  have := subtype.eq hh,
  simpa using this
end

lemma Bij_on.injective (h : Bij_on f univ b) : function.injective f :=
injective_iff_inj_on_univ.mpr h.inj_on

lemma Bij_on.right_inv (h : Bij_on f a b) (y) : f (h.e.symm y) = y :=
by rw h.he; simp

@[refl] def Bij_on.refl (a : set α) : Bij_on id a a :=
{ e := equiv.refl _, he := assume x, rfl }

@[trans] def Bij_on.trans {f : α → β} {g : β → γ}
  {a : set α} {b : set β} {c : set γ} (hf : Bij_on f a b) (hg : Bij_on g b c) :
  Bij_on (g ∘ f) a c :=
{ e := hf.e.trans hg.e,
  he := assume x, show g (f x) = hg.e (hf.e x), by rw [hf.he, hg.he] }

def Bij_on.trans_symm {f : α → β} {g : β → γ}
  {a : set α} {b : set β} {c : set γ} (hf : ∀ x, x ∈ a → f x ∈ b)
  (hgf : Bij_on (g ∘ f) a c) (hg : Bij_on g b c) :
  Bij_on f a b :=
{ e := hgf.e.trans hg.e.symm,
  he := assume x, show f x = hg.e.symm (hgf.e x), begin
    apply hg.inj_on,
    exact hf x.val x.property,
    exact (hg.e.symm (hgf.e x)).property,
    change (g ∘ f) x = _,
    rw [hg.he, hgf.he], simp
  end }

-- Product of two bijections.
def Bij_on.prod {f : α → β} {a : set α} {b : set β}
  {g : γ → δ} {c : set γ} {d : set δ} (hf : Bij_on f a b) (hg : Bij_on g c d) :
  Bij_on (λ (p : α × γ), (f p.1, g p.2)) (a.prod c) (b.prod d) :=
{ e :=
  -- This is a bit ugly. But building e out of equiv.prod_congr made
  -- the proof of `he` more difficult. Part of the problem is that
  -- `equiv.set.prod` is too "strict": its to_fun pattern matches on
  -- its argument.
  { to_fun := λ p,
      ⟨(hf.e ⟨p.1.1, p.2.1⟩, hg.e ⟨p.1.2, p.2.2⟩),
       ⟨(hf.e ⟨p.1.1, p.2.1⟩).property, (hg.e ⟨p.1.2, p.2.2⟩).property⟩⟩,
    inv_fun := λ p,
      ⟨(hf.e.symm ⟨p.1.1, p.2.1⟩, hg.e.symm ⟨p.1.2, p.2.2⟩),
       ⟨(hf.e.symm ⟨p.1.1, p.2.1⟩).property, (hg.e.symm ⟨p.1.2, p.2.2⟩).property⟩⟩,
    left_inv := λ ⟨⟨x, y⟩, ⟨hx, hy⟩⟩, by simp,
    right_inv := λ ⟨⟨x, y⟩, ⟨hx, hy⟩⟩, by simp },
  he := λ ⟨⟨x, y⟩, ⟨hx, hy⟩⟩, show (f (subtype.mk x hx), g (subtype.mk y hy)) = _,
    by rw [hf.he, hg.he]; simp }

-- Product of two total bijections.
-- Again, we need to use this instead of `equiv.prod_congr` because
-- the latter is too strict.
def Bij_on.prod' {f : α → β} {g : γ → δ}
  (hf : Bij_on f univ univ) (hg : Bij_on g univ univ) :
  Bij_on (λ (p : α × γ), (f p.1, g p.2)) univ univ :=
begin convert Bij_on.prod hf hg; ext p; simp end

-- Product of a total bijection by a type.
def Bij_on.prod_right' {f : α → β} {b : set β} (hf : Bij_on f univ b) :
  Bij_on (λ (p : α × γ), (f p.1, p.2)) univ (b.prod univ) :=
by convert Bij_on.prod hf (Bij_on.refl univ); simp

-- Restriction of a bijection to a subset.
def Bij_on.restrict (h : Bij_on f a b) (r : set β) : Bij_on f (f ⁻¹' r ∩ a) (r ∩ b) :=
{ e :=
  { to_fun := λ p,
      ⟨h.e ⟨p.val, p.property.right⟩,
       by rw ←h.he; exact p.property.left,
       (h.e _).property⟩,
    inv_fun := λ p,
      ⟨h.e.symm ⟨p.val, p.property.right⟩,
       by rw [mem_preimage_eq, h.he]; simpa using p.property.left,
       (h.e.symm _).property⟩,
    left_inv := λ ⟨p, hp⟩, by simp,
    right_inv := λ ⟨p, hp⟩, by simp },
  he := λ ⟨p, hp⟩, by change f p = _; rw h.he' hp.right; simp }

-- Restriction of a total bijection to a subset.
def Bij_on.restrict' (h : Bij_on f univ b) (r : set β) : Bij_on f (f ⁻¹' r) (r ∩ b) :=
by convert Bij_on.restrict h r; simp

def Bij_on.restrict'' (h : Bij_on f univ univ) (r : set β) : Bij_on f (f ⁻¹' r) r :=
by convert Bij_on.restrict' h r; simp

def Bij_on.restrict_equiv (e : α ≃ β) (r : set β) : Bij_on e.to_fun (e.to_fun ⁻¹' r) r :=
(Bij_on.of_equiv e).restrict'' r

-- Restriction of a bijection to a subtype on both sides.
-- TODO: Reduce duplicated ugliness with Bij_on.restrict?
def Bij_on.restrict_to_subtype (h : Bij_on f a b) (r : β → Prop) :
  Bij_on (λ (x : subtype (f ⁻¹' r)), (⟨f x.val, x.property⟩ : subtype r))
    {x | x.val ∈ a} {y | y.val ∈ b} :=
{ e :=
  { to_fun := λ p,
      ⟨⟨h.e ⟨p.val.val, p.property⟩,
       by rw ←h.he; exact p.val.property⟩,
       (h.e _).property⟩,
    inv_fun := λ p,
      ⟨⟨h.e.symm ⟨p.val.val, p.property⟩,
       show ↑(h.e.symm ⟨p.val.val, p.property⟩) ∈ f ⁻¹' r, from
       by rw [mem_preimage_eq, h.he]; simpa using p.val.property⟩,
       (h.e.symm _).property⟩,
    left_inv := λ ⟨p, hp⟩, by simp,
    right_inv := λ ⟨p, hp⟩, by simp },
  he := λ ⟨p, hp⟩, by apply subtype.eq; change f p = _; rw h.he'; simpa }

-- Bijection between a subtype and a propositionally equal one.
def Bij_on.congr_subtype {r r' : set α} (h : r = r') :
  Bij_on (λ (x : subtype r), (⟨x, _⟩ : subtype r')) univ univ :=
Bij_on.of_equiv $ equiv.subtype_equiv_subtype h

end Bij_on


