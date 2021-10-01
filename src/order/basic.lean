/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro
-/
import data.subtype
import data.prod

/-!
# Basic definitions about `≤` and `<`

## Definitions

- `order_dual α` : A type tag reversing the meaning of all inequalities.

### Predicates on functions

* `monotone f`: A function between two types equipped with `≤` is monotone if `a ≤ b` implies
  `f a ≤ f b`.
* `antitone f`: A function between two types equipped with `≤` is antitone if `a ≤ b` implies
  `f b ≤ f a`.
* `strict_mono f` : A function between two types equipped with `<` is strictly monotone if
  `a < b` implies `f a < f b`.
* `strict_anti f` : A function between two types equipped with `<` is strictly antitone if
  `a < b` implies `f b < f a`.
* `strict_mono_on f s`: Same as `strict_mono f`, but for all `a, b ∈ s`.
* `strict_anti_on f s`: Same as `strict_anti f`, but for all `a, b ∈ s`.

### Transfering orders

- `order.preimage`, `preorder.lift`: Transfers a (pre)order on `β` to an order on `α`
  using a function `f : α → β`.
- `partial_order.lift`, `linear_order.lift`: Transfers a partial (resp., linear) order on `β` to a
  partial (resp., linear) order on `α` using an injective function `f`.

### Extra classes

- `no_top_order`, `no_bot_order`: An order without a maximal/minimal element.
- `densely_ordered`: An order with no gap, i.e. for any two elements `a < b` there exists `c` such
  that `a < c < b`.

## Main theorems

- `monotone_nat_of_le_succ`: If `f : ℕ → α` and `f n ≤ f (n + 1)` for all `n`, then `f` is
  monotone.
- `antitone_nat_of_succ_le`: If `f : ℕ → α` and `f (n + 1) ≤ f n` for all `n`, then `f` is
  antitone.
- `strict_mono_nat_of_lt_succ`: If `f : ℕ → α` and `f n < f (n + 1)` for all `n`, then `f` is
  strictly monotone.
- `strict_anti_nat_of_succ_lt`: If `f : ℕ → α` and `f (n + 1) < f n` for all `n`, then `f` is
  strictly antitone.

## TODO

- expand module docs
- automatic construction of dual definitions / theorems

## See also

- `algebra.order.basic` for basic lemmas about orders, and projection notation for orders

## Tags

preorder, order, partial order, linear order, monotone, strictly monotone
-/

open function

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w} {r : α → α → Prop}

attribute [simp] le_refl

@[simp] lemma lt_self_iff_false [preorder α] (a : α) : a < a ↔ false :=
⟨lt_irrefl a, false.elim⟩

attribute [ext] has_le

@[ext]
lemma preorder.to_has_le_injective {α : Type*} :
  function.injective (@preorder.to_has_le α) :=
λ A B h, begin
  cases A, cases B,
  injection h with h_le,
  have : A_lt = B_lt,
  { funext a b,
    dsimp [(≤)] at A_lt_iff_le_not_le B_lt_iff_le_not_le h_le,
    simp [A_lt_iff_le_not_le, B_lt_iff_le_not_le, h_le], },
  congr',
end

@[ext]
lemma partial_order.to_preorder_injective {α : Type*} :
  function.injective (@partial_order.to_preorder α) :=
λ A B h, by { cases A, cases B, injection h, congr' }

@[ext]
lemma linear_order.to_partial_order_injective {α : Type*} :
  function.injective (@linear_order.to_partial_order α) :=
begin
  intros A B h,
  cases A, cases B, injection h,
  obtain rfl : A_le = B_le := ‹_›, obtain rfl : A_lt = B_lt := ‹_›,
  obtain rfl : A_decidable_le = B_decidable_le := subsingleton.elim _ _,
  obtain rfl : A_max = B_max := A_max_def.trans B_max_def.symm,
  obtain rfl : A_min = B_min := A_min_def.trans B_min_def.symm,
  congr
end

theorem preorder.ext {α} {A B : preorder α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem partial_order.ext {α} {A B : partial_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

theorem linear_order.ext {α} {A B : linear_order α}
  (H : ∀ x y : α, (by haveI := A; exact x ≤ y) ↔ x ≤ y) : A = B :=
by { ext x y, exact H x y }

/-- Given a relation `R` on `β` and a function `f : α → β`, the preimage relation on `α` is defined
by `x ≤ y ↔ f x ≤ f y`. It is the unique relation on `α` making `f` a `rel_embedding` (assuming `f`
is injective). -/
@[simp] def order.preimage {α β} (f : α → β) (s : β → β → Prop) (x y : α) : Prop := s (f x) (f y)

infix ` ⁻¹'o `:80 := order.preimage

/-- The preimage of a decidable order is decidable. -/
instance order.preimage.decidable {α β} (f : α → β) (s : β → β → Prop) [H : decidable_rel s] :
  decidable_rel (f ⁻¹'o s) :=
λ x y, H _ _

section monotone
variables [preorder α] [preorder β] [preorder γ]

/-- A function between preorders is monotone if `a ≤ b` implies `f a ≤ f b`. -/
def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b

/-- A function between preorders is antitone if `a ≤ b` implies `f b ≤ f a`. -/
def antitone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f b ≤ f a

theorem monotone_id : @monotone α α _ _ id := λ x y h, h

theorem monotone_const {b : β} : monotone (λ (a : α), b) := λ x y h, le_refl b

theorem antitone_const {b : β} : antitone (λ (a : α), b) := λ x y h, le_refl b

protected theorem monotone.comp {g : β → γ} {f : α → β} (m_g : monotone g) (m_f : monotone f) :
  monotone (g ∘ f) :=
λ a b h, m_g (m_f h)

lemma monotone.comp_antitone {g : β → γ} {f : α → β} (m_g : monotone g) (m_f : antitone f) :
  antitone (g ∘ f) :=
λ a b h, m_g (m_f h)

protected theorem antitone.comp {g : β → γ} {f : α → β} (m_g : antitone g) (m_f : antitone f) :
  monotone (g ∘ f) :=
λ a b h, m_g (m_f h)

theorem antitone.comp_monotone {g : β → γ} {f : α → β} (m_g : antitone g) (m_f : monotone f) :
  antitone (g ∘ f) :=
λ a b h, m_g (m_f h)

protected theorem monotone.iterate {f : α → α} (hf : monotone f) (n : ℕ) : monotone (f^[n]) :=
nat.rec_on n monotone_id (λ n ihn, ihn.comp hf)

protected lemma monotone.apply_max {α β : Type*} [linear_order α] [linear_order β] {f : α → β}
  (hf : monotone f) (a b : α) :
  f (max a b) = max (f a) (f b) :=
begin
  cases le_total a b,
  { rw [max_eq_right h, max_eq_right (hf h)] },
  { rw [max_eq_left h, max_eq_left (hf h)] }
end

protected lemma antitone.apply_max {α β : Type*} [linear_order α] [linear_order β] {f : α → β}
  (hf : antitone f) (a b : α) :
  f (max a b) = min (f a) (f b) :=
begin
  cases le_total a b,
  { rw [max_eq_right h, min_eq_right (hf h)] },
  { rw [max_eq_left h, min_eq_left (hf h)] }
end

protected lemma monotone.apply_min {α β : Type*} [linear_order α] [linear_order β] {f : α → β}
  (hf : monotone f) (a b : α) :
  f (min a b) = min (f a) (f b) :=
begin
  cases le_total a b,
  { rw [min_eq_left h, min_eq_left (hf h)] },
  { rw [min_eq_right h, min_eq_right (hf h)] }
end

protected lemma antitone.apply_min {α β : Type*} [linear_order α] [linear_order β] {f : α → β}
  (hf : antitone f) (a b : α) :
  f (min a b) = max (f a) (f b) :=
begin
  cases le_total a b,
  { rw [min_eq_left h, max_eq_left (hf h)] },
  { rw [min_eq_right h, max_eq_right (hf h)] }
end

lemma monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) :
  monotone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, assumption, exact hf _ }
end

lemma antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) :
  antitone f | n m h :=
begin
  induction h,
  { refl },
  { transitivity, exact hf _, assumption }
end

lemma monotone.reflect_lt {α β} [linear_order α] [preorder β] {f : α → β} (hf : monotone f)
  {x x' : α} (h : f x < f x') : x < x' :=
lt_of_not_ge (λ h', h.not_le (hf h'))

lemma antitone.reflect_lt {α β} [linear_order α] [preorder β] {f : α → β} (hf : antitone f)
  {x x' : α} (h : f x < f x') : x' < x :=
lt_of_not_ge (λ h', h.not_le (hf h'))

-- TODO@Yael: Generalize to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_nat {α} [preorder α] {f : ℕ → α} (hf : monotone f) (n : ℕ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℕ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (nat.le_of_lt_succ $ hf.reflect_lt h2) }

-- TODO@Yael: Generalize to succ orders
/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_nat {α} [preorder α] {f : ℕ → α} (hf : antitone f)
  (n : ℕ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (nat.le_of_lt_succ $ hf.reflect_lt h1) }

/-- If `f` is a monotone function from `ℤ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
lemma monotone.ne_of_lt_of_lt_int {α} [preorder α] {f : ℤ → α} (hf : monotone f) (n : ℤ) {x : α}
  (h1 : f n < x) (h2 : x < f (n + 1)) (a : ℤ) :
  f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h1).not_le (int.le_of_lt_add_one $ hf.reflect_lt h2) }

/-- If `f` is an antitone function from `ℤ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
lemma antitone.ne_of_lt_of_lt_int {α} [preorder α] {f : ℤ → α} (hf : antitone f)
  (n : ℤ) {x : α} (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x :=
by { rintro rfl, exact (hf.reflect_lt h2).not_le (int.le_of_lt_add_one $ hf.reflect_lt h1) }

end monotone

/-- A function `f` is strictly monotone if `a < b` implies `f a < f b`. -/
def strict_mono [has_lt α] [has_lt β] (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f a < f b

/-- A function `f` is strictly antitone if `a < b` implies `f b < f a`. -/
def strict_anti [has_lt α] [has_lt β] (f : α → β) : Prop :=
∀ ⦃a b⦄, a < b → f b < f a

lemma strict_mono_id [has_lt α] : strict_mono (id : α → α) := λ a b, id

/-- A function `f` is strictly monotone increasing on `t` if `x < y` for `x,y ∈ t` implies
`f x < f y`. -/
def strict_mono_on [has_lt α] [has_lt β] (f : α → β) (t : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ t) ⦃y⦄ (hy : y ∈ t), x < y → f x < f y

/-- A function `f` is strictly monotone decreasing on `t` if `x < y` for `x,y ∈ t` implies
`f y < f x`. -/
def strict_anti_on [has_lt α] [has_lt β] (f : α → β) (t : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ t) ⦃y⦄ (hy : y ∈ t), x < y → f y < f x

/-- Type tag for a set with dual order: `≤` means `≥` and `<` means `>`. -/
def order_dual (α : Type*) : Type* := α

namespace order_dual

instance (α : Type*) [h : nonempty α] : nonempty (order_dual α) := h
instance (α : Type*) [h : subsingleton α] : subsingleton (order_dual α) := h
instance (α : Type*) [has_le α] : has_le (order_dual α) := ⟨λ x y : α, y ≤ x⟩
instance (α : Type*) [has_lt α] : has_lt (order_dual α) := ⟨λ x y : α, y < x⟩
instance (α : Type*) [has_zero α] : has_zero (order_dual α) := ⟨(0 : α)⟩

-- `dual_le` and `dual_lt` should not be simp lemmas:
-- they cause a loop since `α` and `order_dual α` are definitionally equal

lemma dual_le [has_le α] {a b : α} :
  @has_le.le (order_dual α) _ a b ↔ @has_le.le α _ b a := iff.rfl

lemma dual_lt [has_lt α] {a b : α} :
  @has_lt.lt (order_dual α) _ a b ↔ @has_lt.lt α _ b a := iff.rfl

lemma dual_compares [has_lt α] {a b : α} {o : ordering} :
  @ordering.compares (order_dual α) _ o a b ↔ @ordering.compares α _ o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

instance (α : Type*) [preorder α] : preorder (order_dual α) :=
{ le_refl          := le_refl,
  le_trans         := λ a b c hab hbc, hbc.trans hab,
  lt_iff_le_not_le := λ _ _, lt_iff_le_not_le,
  .. order_dual.has_le α,
  .. order_dual.has_lt α }

instance (α : Type*) [partial_order α] : partial_order (order_dual α) :=
{ le_antisymm := λ a b hab hba, @le_antisymm α _ a b hba hab, .. order_dual.preorder α }

instance (α : Type*) [linear_order α] : linear_order (order_dual α) :=
{ le_total     := λ a b : α, le_total b a,
  decidable_le := (infer_instance : decidable_rel (λ a b : α, b ≤ a)),
  decidable_lt := (infer_instance : decidable_rel (λ a b : α, b < a)),
  min := @max α _,
  max := @min α _,
  min_def := @linear_order.max_def α _,
  max_def := @linear_order.min_def α _,
  .. order_dual.partial_order α }

instance : Π [inhabited α], inhabited (order_dual α) := id

theorem preorder.dual_dual (α : Type*) [H : preorder α] :
  order_dual.preorder (order_dual α) = H :=
preorder.ext $ λ _ _, iff.rfl

theorem partial_order.dual_dual (α : Type*) [H : partial_order α] :
  order_dual.partial_order (order_dual α) = H :=
partial_order.ext $ λ _ _, iff.rfl

theorem linear_order.dual_dual (α : Type*) [H : linear_order α] :
  order_dual.linear_order (order_dual α) = H :=
linear_order.ext $ λ _ _, iff.rfl

theorem cmp_le_flip {α} [has_le α] [@decidable_rel α (≤)] (x y : α) :
  @cmp_le (order_dual α) _ _ x y = cmp_le y x := rfl

end order_dual

namespace strict_mono_on

section dual

variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected lemma dual (H : strict_mono_on f s) :
  @strict_mono_on (order_dual α) (order_dual β) _ _ f s :=
λ x hx y hy, H hy hx

protected lemma dual_right (H : strict_mono_on f s) :
  @strict_anti_on α (order_dual β) _ _ f s :=
H

end dual

variables [linear_order α] [preorder β] {f : α → β} {s : set α} {x y : α}

lemma le_iff_le (H : strict_mono_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x ≤ f y ↔ x ≤ y :=
⟨λ h, le_of_not_gt $ λ h', not_le_of_lt (H hy hx h') h,
 λ h, h.lt_or_eq_dec.elim (λ h', le_of_lt (H hx hy h')) (λ h', h' ▸ le_refl _)⟩

lemma lt_iff_lt (H : strict_mono_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x < f y ↔ x < y :=
by simp only [H.le_iff_le, hx, hy, lt_iff_le_not_le]

protected theorem compares (H : strict_mono_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  ∀ {o}, ordering.compares o (f x) (f y) ↔ ordering.compares o x y
| ordering.lt := H.lt_iff_lt hx hy
| ordering.eq := ⟨λ h, ((H.le_iff_le hx hy).1 h.le).antisymm ((H.le_iff_le hy hx).1 h.symm.le),
                   congr_arg _⟩
| ordering.gt := H.lt_iff_lt hy hx

end strict_mono_on

namespace strict_anti_on

section dual

variables [preorder α] [preorder β] {f : α → β} {s : set α}

protected lemma dual (H : strict_anti_on f s) :
  @strict_anti_on (order_dual α) (order_dual β) _ _ f s :=
λ x hx y hy, H hy hx

protected lemma dual_right (H : strict_anti_on f s) :
  @strict_mono_on α (order_dual β) _ _ f s :=
H

end dual

variables [linear_order α] [preorder β] {f : α → β} {s : set α} {x y : α}

lemma le_iff_le (H : strict_anti_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x ≤ f y ↔ y ≤ x :=
H.dual_right.le_iff_le hy hx

lemma lt_iff_lt (H : strict_anti_on f s) (hx : x ∈ s) (hy : y ∈ s) :
  f x < f y ↔ y < x :=
H.dual_right.lt_iff_lt hy hx

protected theorem compares (H : strict_anti_on f s) (hx : x ∈ s) (hy : y ∈ s) {o : ordering} :
  ordering.compares o (f x) (f y) ↔ ordering.compares o y x :=
order_dual.dual_compares.trans $ H.dual_right.compares hy hx

end strict_anti_on

namespace strict_mono
open ordering function

protected lemma strict_mono_on [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f)
  (s : set α) :
  strict_mono_on f s :=
λ x hx y hy hxy, hf hxy


lemma comp [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_mono g) (hf : strict_mono f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma comp_strict_anti [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_mono g) (hf : strict_anti f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected theorem iterate [has_lt α] {f : α → α} (hf : strict_mono f) (n : ℕ) :
  strict_mono (f^[n]) :=
nat.rec_on n strict_mono_id (λ n ihn, ihn.comp hf)

lemma id_le {φ : ℕ → ℕ} (h : strict_mono φ) : ∀ n, n ≤ φ n :=
λ n, nat.rec_on n (nat.zero_le _)
  (λ n hn, nat.succ_le_of_lt (hn.trans_lt $ h n.lt_succ_self))

protected lemma ite' [preorder α] [has_lt β] {f g : α → β} (hf : strict_mono f) (hg : strict_mono g)
  {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → f x < g y) :
  strict_mono (λ x, if p x then f x else g x) :=
begin
  intros x y h,
  by_cases hy : p y,
  { have hx : p x := hp h hy,
    simpa [hx, hy] using hf h },
  { by_cases hx : p x,
    { simpa [hx, hy] using hfg hx hy h },
    { simpa [hx, hy] using hg h} }
end

protected lemma ite [preorder α] [preorder β] {f g : α → β} (hf : strict_mono f)
  (hg : strict_mono g) {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ x, f x ≤ g x) :
  strict_mono (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hf h).trans_le (hfg y)

section
variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} : f a < f b ↔ a < b :=
(H.strict_mono_on set.univ).lt_iff_lt trivial trivial

protected theorem compares (H : strict_mono f) {a b} {o} :
  compares o (f a) (f b) ↔ compares o a b :=
(H.strict_mono_on set.univ).compares trivial trivial

lemma injective (H : strict_mono f) : injective f :=
λ x y h, show compares eq x y, from H.compares.1 h

lemma le_iff_le (H : strict_mono f) {a b} : f a ≤ f b ↔ a ≤ b :=
(H.strict_mono_on set.univ).le_iff_le trivial trivial

lemma maximal_preimage_top (H : strict_mono f) {a} (h_top : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
H.le_iff_le.mp (h_top (f x))

lemma minimal_preimage_bot (H : strict_mono f) {a} (h_bot : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
H.le_iff_le.mp (h_bot (f x))

end

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,
-- then `strict_mono f` is vacuously true.
lemma monotone [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
λ a b h, (lt_or_eq_of_le h).rec (le_of_lt ∘ (@H _ _)) (by rintro rfl; refl)

end strict_mono

namespace strict_anti
open ordering function

protected lemma strict_anti_on [has_lt α] [has_lt β] {f : α → β} (hf : strict_anti f)
  (s : set α) :
  strict_anti_on f s :=
λ x hx y hy hxy, hf hxy

lemma comp [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_anti g) (hf : strict_anti f) :
  strict_mono (g ∘ f) :=
λ a b h, hg (hf h)

lemma comp_strict_mono [has_lt α] [has_lt β] [has_lt γ] {g : β → γ} {f : α → β}
  (hg : strict_anti g) (hf : strict_mono f) :
  strict_anti (g ∘ f) :=
λ a b h, hg (hf h)

protected lemma ite' [preorder α] [has_lt β] {f g : α → β} (hf : strict_anti f) (hg : strict_anti g)
  {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ ⦃x y⦄, p x → ¬p y → x < y → g y < f x) :
  strict_anti (λ x, if p x then f x else g x) :=
begin
  intros x y h,
  by_cases hy : p y,
  { have hx : p x := hp h hy,
    simpa [hx, hy] using hf h },
  by_cases hx : p x,
  { simpa [hx, hy] using hfg hx hy h },
  { simpa [hx, hy] using hg h }
end

protected lemma ite [preorder α] [preorder β] {f g : α → β} (hf : strict_anti f)
  (hg : strict_anti g) {p : α → Prop} [decidable_pred p] (hp : ∀ ⦃x y⦄, x < y → p y → p x)
  (hfg : ∀ x, g x ≤ f x) :
  strict_anti (λ x, if p x then f x else g x) :=
hf.ite' hg hp $ λ x y hx hy h, (hfg y).trans_lt (hf h)

section
variables [linear_order α] [preorder β] {f : α → β}

lemma lt_iff_lt (H : strict_mono f) {a b} : f a < f b ↔ a < b :=
(H.strict_mono_on set.univ).lt_iff_lt trivial trivial

protected theorem compares (H : strict_mono f) {a b} {o} :
  compares o (f a) (f b) ↔ compares o a b :=
(H.strict_mono_on set.univ).compares trivial trivial

lemma injective (H : strict_mono f) : injective f :=
λ x y h, show compares eq x y, from H.compares.1 h

lemma le_iff_le (H : strict_mono f) {a b} : f a ≤ f b ↔ a ≤ b :=
(H.strict_mono_on set.univ).le_iff_le trivial trivial

lemma top_preimage_top (H : strict_mono f) {a} (h_top : ∀ p, p ≤ f a) (x : α) : x ≤ a :=
H.le_iff_le.mp (h_top (f x))

lemma bot_preimage_bot (H : strict_mono f) {a} (h_bot : ∀ p, f a ≤ p) (x : α) : a ≤ x :=
H.le_iff_le.mp (h_bot (f x))

end

-- `preorder α` isn't strong enough: if the preorder on α is an equivalence relation,
-- then `strict_mono f` is vacuously true.
lemma monotone [partial_order α] [preorder β] {f : α → β} (H : strict_mono f) : monotone f :=
λ a b h, (lt_or_eq_of_le h).rec (le_of_lt ∘ (@H _ _)) (by rintro rfl; refl)

end strict_anti

-- TODO@Yael: Generalize to succ orders
lemma strict_mono_nat_of_lt_succ {β} [preorder β] {f : ℕ → β} (h : ∀ n, f n < f (n + 1)) :
  strict_mono f :=
by { intros n m hnm, induction hnm with m' hnm' ih, apply h, exact ih.trans (h _) }

section
open function

lemma injective_of_lt_imp_ne [linear_order α] {f : α → β} (h : ∀ x y, x < y → f x ≠ f y) :
  injective f :=
begin
  intros x y k,
  contrapose k,
  rw [←ne.def, ne_iff_lt_or_gt] at k,
  cases k,
  { apply h _ _ k },
  { rw eq_comm,
    apply h _ _ k }
end

lemma injective_of_le_imp_le [partial_order α] [preorder β] (f : α → β)
  (h : ∀ {x y}, f x ≤ f y → x ≤ y) : injective f :=
λ x y hxy, (h hxy.le).antisymm (h hxy.ge)

lemma monotone.strict_mono_of_injective [partial_order α] [partial_order β] {f : α → β}
  (h₁ : monotone f) (h₂ : injective f) : strict_mono f :=
λ a b h,
begin
  rw lt_iff_le_and_ne at ⊢ h,
  exact ⟨h₁ h.1, λ e, h.2 (h₂ e)⟩
end

lemma monotone.strict_mono_iff_injective [linear_order α] [partial_order β] {f : α → β}
  (h : monotone f) : strict_mono f ↔ injective f :=
⟨λ h, h.injective, h.strict_mono_of_injective⟩

lemma strict_mono_of_le_iff_le [preorder α] [preorder β] {f : α → β}
  (h : ∀ x y, x ≤ y ↔ f x ≤ f y) : strict_mono f :=
λ a b, by simp [lt_iff_le_not_le, h] {contextual := tt}

end

/-! ### Order instances on the function space -/

instance pi.preorder {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] : preorder (Π i, α i) :=
{ le       := λ x y, ∀ i, x i ≤ y i,
  le_refl  := λ a i, le_refl (a i),
  le_trans := λ a b c h₁ h₂ i, le_trans (h₁ i) (h₂ i) }

lemma function.monotone_eval {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] (i : ι) :
  monotone (function.eval i : (Π i, α i) → α i) :=
λ f g H, H i

lemma pi.le_def {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] {x y : Π i, α i} :
  x ≤ y ↔ ∀ i, x i ≤ y i :=
iff.rfl

lemma pi.lt_def {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] {x y : Π i, α i} :
  x < y ↔ x ≤ y ∧ ∃ i, x i < y i :=
by simp [lt_iff_le_not_le, pi.le_def] {contextual := tt}

lemma le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  x ≤ function.update y i a ↔ x i ≤ a ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, x j ≤ z)

lemma update_le_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a : α i} :
  function.update x i a ≤ y ↔ a ≤ y i ∧ ∀ j ≠ i, x j ≤ y j :=
function.forall_update_iff _ (λ j z, z ≤ y j)

lemma update_le_update_iff {ι : Type u} {α : ι → Type v} [∀ i, preorder (α i)] [decidable_eq ι]
  {x y : Π i, α i} {i : ι} {a b : α i} :
  function.update x i a ≤ function.update y i b ↔ a ≤ b ∧ ∀ j ≠ i, x j ≤ y j :=
by simp [update_le_iff] {contextual := tt}

instance pi.partial_order {ι : Type u} {α : ι → Type v} [∀ i, partial_order (α i)] :
  partial_order (Πi, α i) :=
{ le_antisymm := λ f g h1 h2, funext (λ b, (h1 b).antisymm (h2 b)),
  ..pi.preorder }

theorem comp_le_comp_left_of_monotone [preorder α] [preorder β]
  {f : β → α} {g h : γ → β} (m_f : monotone f) (le_gh : g ≤ h) :
  has_le.le.{max w u} (f ∘ g) (f ∘ h) :=
λ x, m_f (le_gh x)

section monotone
variables [preorder α] [preorder γ]

protected theorem monotone.order_dual {f : α → γ} (hf : monotone f) :
  @monotone (order_dual α) (order_dual γ) _ _ f :=
λ x y hxy, hf hxy

protected lemma monotone.order_dual_left {f : α → γ} (hf : monotone f) :
  @antitone (order_dual α) γ _ _ f :=
λ x y hxy, hf hxy

protected lemma monotone.order_dual_right {f : α → γ} (hf : monotone f) :
  @antitone α (order_dual γ) _ _ f :=
λ x y hxy, hf hxy

theorem monotone_lam {f : α → β → γ} (m : ∀ b, monotone (λ a, f a b)) : monotone f :=
λ a a' h b, m b h

theorem monotone_app (f : β → α → γ) (b : β) (m : monotone (λ a b, f b a)) : monotone (f b) :=
λ a a' h, m h b

end monotone

section antitone
variables [preorder α] [preorder γ]

protected theorem antitone.order_dual {f : α → γ} (hf : antitone f) :
  @antitone (order_dual α) (order_dual γ) _ _ f :=
λ x y hxy, hf hxy

protected lemma antitone.order_dual_left {f : α → γ} (hf : antitone f) :
  @monotone (order_dual α) γ _ _ f :=
λ x y hxy, hf hxy

protected lemma antitone.order_dual_right {f : α → γ} (hf : antitone f) :
  @monotone α (order_dual γ) _ _ f :=
λ x y hxy, hf hxy

theorem antitone_lam {f : α → β → γ} (m : ∀ b, antitone (λ a, f a b)) : antitone f :=
λ a a' h b, m b h

theorem antitone_app (f : β → α → γ) (b : β) (m : antitone (λ a b, f b a)) : antitone (f b) :=
λ a a' h, m h b

end antitone

theorem strict_mono.order_dual [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f) :
  @strict_mono (order_dual α) (order_dual β) _ _ f :=
λ x y hxy, hf hxy

lemma strict_mono.order_dual_left [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f) :
  @strict_anti (order_dual α) β _ _ f :=
λ x y hxy, hf hxy

lemma strict_mono.order_dual_right [has_lt α] [has_lt β] {f : α → β} (hf : strict_mono f) :
  @strict_anti α (order_dual β) _ _ f :=
λ x y hxy, hf hxy

lemma strict_anti.order_dual [has_lt α] [has_lt β] {f : α → β} (hf : strict_anti f) :
  @strict_anti (order_dual α) (order_dual β) _ _ f :=
λ x y hxy, hf hxy

lemma strict_anti.order_dual_left [has_lt α] [has_lt β] {f : α → β} (hf : strict_anti f) :
  @strict_mono (order_dual α) β _ _ f :=
λ x y hxy, hf hxy

lemma strict_anti.order_dual_right [has_lt α] [has_lt β] {f : α → β} (hf : strict_anti f) :
  @strict_mono α (order_dual β) _ _ f :=
λ x y hxy, hf hxy

/-- Transfer a `preorder` on `β` to a `preorder` on `α` using a function `f : α → β`.
See note [reducible non-instances]. -/
@[reducible] def preorder.lift {α β} [preorder β] (f : α → β) : preorder α :=
{ le               := λ x y, f x ≤ f y,
  le_refl          := λ a, le_refl _,
  le_trans         := λ a b c, le_trans,
  lt               := λ x y, f x < f y,
  lt_iff_le_not_le := λ a b, lt_iff_le_not_le }

/-- Transfer a `partial_order` on `β` to a `partial_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def partial_order.lift {α β} [partial_order β] (f : α → β) (inj : injective f) :
  partial_order α :=
{ le_antisymm := λ a b h₁ h₂, inj (h₁.antisymm h₂), .. preorder.lift f }

/-- Transfer a `linear_order` on `β` to a `linear_order` on `α` using an injective
function `f : α → β`. See note [reducible non-instances]. -/
@[reducible] def linear_order.lift {α β} [linear_order β] (f : α → β) (inj : injective f) :
  linear_order α :=
{ le_total     := λ x y, le_total (f x) (f y),
  decidable_le := λ x y, (infer_instance : decidable (f x ≤ f y)),
  decidable_lt := λ x y, (infer_instance : decidable (f x < f y)),
  decidable_eq := λ x y, decidable_of_iff _ inj.eq_iff,
  .. partial_order.lift f inj }

instance subtype.preorder {α} [preorder α] (p : α → Prop) : preorder (subtype p) :=
preorder.lift subtype.val

@[simp] lemma subtype.mk_le_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) ≤ ⟨y, hy⟩ ↔ x ≤ y :=
iff.rfl

@[simp] lemma subtype.mk_lt_mk {α} [preorder α] {p : α → Prop} {x y : α} {hx : p x} {hy : p y} :
  (⟨x, hx⟩ : subtype p) < ⟨y, hy⟩ ↔ x < y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_le_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) ≤ y ↔ x ≤ y :=
iff.rfl

@[simp, norm_cast] lemma subtype.coe_lt_coe {α} [preorder α] {p : α → Prop} {x y : subtype p} :
  (x : α) < y ↔ x < y :=
iff.rfl

instance subtype.partial_order {α} [partial_order α] (p : α → Prop) :
  partial_order (subtype p) :=
partial_order.lift subtype.val subtype.val_injective

instance subtype.linear_order {α} [linear_order α] (p : α → Prop) : linear_order (subtype p) :=
linear_order.lift subtype.val subtype.val_injective

lemma subtype.mono_coe [preorder α] (t : set α) : monotone (coe : (subtype t) → α) :=
λ x y, id

lemma subtype.strict_mono_coe [preorder α] (t : set α) : strict_mono (coe : (subtype t) → α) :=
λ x y, id

namespace prod

instance (α : Type u) (β : Type v) [has_le α] [has_le β] : has_le (α × β) :=
⟨λ p q, p.1 ≤ q.1 ∧ p.2 ≤ q.2⟩

lemma le_def {α β : Type*} [has_le α] [has_le β] {x y : α × β} :
  x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2 := iff.rfl

@[simp] lemma mk_le_mk {α β : Type*} [has_le α] [has_le β] {x₁ x₂ : α} {y₁ y₂ : β} :
  (x₁, y₁) ≤ (x₂, y₂) ↔ x₁ ≤ x₂ ∧ y₁ ≤ y₂ :=
iff.rfl

instance (α : Type u) (β : Type v) [preorder α] [preorder β] : preorder (α × β) :=
{ le_refl  := λ ⟨a, b⟩, ⟨le_refl a, le_refl b⟩,
  le_trans := λ ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ ⟨hac, hbd⟩ ⟨hce, hdf⟩,
    ⟨le_trans hac hce, le_trans hbd hdf⟩,
  .. prod.has_le α β }

/-- The pointwise partial order on a product.
    (The lexicographic ordering is defined in order/lexicographic.lean, and the instances are
    available via the type synonym `lex α β = α × β`.) -/
instance (α : Type u) (β : Type v) [partial_order α] [partial_order β] :
  partial_order (α × β) :=
{ le_antisymm := λ ⟨a, b⟩ ⟨c, d⟩ ⟨hac, hbd⟩ ⟨hca, hdb⟩,
    prod.ext (hac.antisymm hca) (hbd.antisymm hdb),
  .. prod.preorder α β }

end prod

lemma monotone_fst {α β : Type*} [preorder α] [preorder β] : monotone (@prod.fst α β) :=
λ x y h, h.1

lemma monotone_snd {α β : Type*} [preorder α] [preorder β] : monotone (@prod.snd α β) :=
λ x y h, h.2

/-!
### Additional order classes
-/

/-- order without a top element; sometimes called cofinal -/
class no_top_order (α : Type u) [preorder α] : Prop :=
(no_top : ∀ a : α, ∃ a', a < a')

lemma no_top [preorder α] [no_top_order α] : ∀ a : α, ∃ a', a < a' :=
no_top_order.no_top

instance nonempty_gt {α : Type u} [preorder α] [no_top_order α] (a : α) :
  nonempty {x // a < x} :=
nonempty_subtype.2 (no_top a)

/-- order without a bottom element; somtimes called coinitial or dense -/
class no_bot_order (α : Type u) [preorder α] : Prop :=
(no_bot : ∀ a : α, ∃ a', a' < a)

lemma no_bot [preorder α] [no_bot_order α] : ∀ a : α, ∃ a', a' < a :=
no_bot_order.no_bot

instance order_dual.no_top_order (α : Type u) [preorder α] [no_bot_order α] :
  no_top_order (order_dual α) :=
⟨λ a, @no_bot α _ _ a⟩

instance order_dual.no_bot_order (α : Type u) [preorder α] [no_top_order α] :
  no_bot_order (order_dual α) :=
⟨λ a, @no_top α _ _ a⟩

instance nonempty_lt {α : Type u} [preorder α] [no_bot_order α] (a : α) :
  nonempty {x // x < a} :=
nonempty_subtype.2 (no_bot a)

/-- An order is dense if there is an element between any pair of distinct elements. -/
class densely_ordered (α : Type u) [preorder α] : Prop :=
(dense : ∀ a₁ a₂ : α, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂)

lemma exists_between [preorder α] [densely_ordered α] :
  ∀ {a₁ a₂ : α}, a₁ < a₂ → ∃ a, a₁ < a ∧ a < a₂ :=
densely_ordered.dense

instance order_dual.densely_ordered (α : Type u) [preorder α] [densely_ordered α] :
  densely_ordered (order_dual α) :=
⟨λ a₁ a₂ ha, (@exists_between α _ _ _ _ ha).imp $ λ a, and.symm⟩

lemma le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀ a, a₂ < a → a₁ ≤ a) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_lt_of_le ‹a < a₁› (h _ ‹a₂ < a›)

lemma eq_of_le_of_forall_le_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a, a₂ < a → a₁ ≤ a) : a₁ = a₂ :=
le_antisymm (le_of_forall_le_of_dense h₂) h₁

lemma le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h : ∀ a₃ < a₁, a₃ ≤ a₂) :
  a₁ ≤ a₂ :=
le_of_not_gt $ λ ha,
  let ⟨a, ha₁, ha₂⟩ := exists_between ha in
  lt_irrefl a $ lt_of_le_of_lt (h _ ‹a < a₁›) ‹a₂ < a›

lemma eq_of_le_of_forall_ge_of_dense [linear_order α] [densely_ordered α] {a₁ a₂ : α}
  (h₁ : a₂ ≤ a₁) (h₂ : ∀ a₃ < a₁, a₃ ≤ a₂) : a₁ = a₂ :=
(le_of_forall_ge_of_dense h₂).antisymm h₁

lemma dense_or_discrete [linear_order α] (a₁ a₂ : α) :
  (∃ a, a₁ < a ∧ a < a₂) ∨ ((∀ a, a₁ < a → a₂ ≤ a) ∧ (∀ a < a₂, a ≤ a₁)) :=
or_iff_not_imp_left.2 $ λ h,
  ⟨λ a ha₁, le_of_not_gt $ λ ha₂, h ⟨a, ha₁, ha₂⟩,
    λ a ha₂, le_of_not_gt $ λ ha₁, h ⟨a, ha₁, ha₂⟩⟩

variables {s : β → β → Prop} {t : γ → γ → Prop}

/-- Type synonym to create an instance of `linear_order` from a `partial_order` and
`is_total α (≤)` -/
def as_linear_order (α : Type u) := α

instance {α} [inhabited α] : inhabited (as_linear_order α) :=
⟨ (default α : α) ⟩

noncomputable instance as_linear_order.linear_order {α} [partial_order α] [is_total α (≤)] :
  linear_order (as_linear_order α) :=
{ le_total     := @total_of α (≤) _,
  decidable_le := classical.dec_rel _,
  .. (_ : partial_order α) }
