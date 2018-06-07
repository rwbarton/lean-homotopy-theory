import data.equiv
import data.set.function

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

end Bij_on


