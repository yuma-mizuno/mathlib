/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module.basic
import data.set.finite
import group_theory.submonoid.basic

/-!
# Pointwise addition, multiplication, and scalar multiplication of sets.

This file defines pointwise algebraic operations on sets.
* For a type `α` with multiplication, multiplication is defined on `set α` by taking
  `s * t` to be the set of all `x * y` where `x ∈ s` and `y ∈ t`. Similarly for addition.
* For `α` a semigroup, `set α` is a semigroup.
* If `α` is a (commutative) monoid, we define an alias `set_semiring α` for `set α`, which then
  becomes a (commutative) semiring with union as addition and pointwise multiplication as
  multiplication.
* For a type `β` with scalar multiplication by another type `α`, this
  file defines a scalar multiplication of `set β` by `set α` and a separate scalar
  multiplication of `set β` by `α`.
* We also define pointwise multiplication on `finset`.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes
* The following expressions are considered in simp-normal form in a group:
  `(λ h, h * g) ⁻¹' s`, `(λ h, g * h) ⁻¹' s`, `(λ h, h * g⁻¹) ⁻¹' s`, `(λ h, g⁻¹ * h) ⁻¹' s`,
  `s * t`, `s⁻¹`, `(1 : set _)` (and similarly for additive variants).
  Expressions equal to one of these will be simplified.
* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`).

## Tags

set multiplication, set addition, pointwise addition, pointwise multiplication

-/

namespace set
open function

variables {α : Type*} {β : Type*} {s s₁ s₂ t t₁ t₂ u : set α} {a b : α} {x y : β}

/-! ### Properties about 1 -/

/-- The set `(1 : set α)` is defined as `{1}` in locale `pointwise`. -/
@[to_additive
/-"The set `(0 : set α)` is defined as `{0}` in locale `pointwise`. "-/]
protected def has_one [has_one α] : has_one (set α) := ⟨{1}⟩

localized "attribute [instance] set.has_one set.has_zero" in pointwise

@[to_additive]
lemma singleton_one [has_one α] : ({1} : set α) = 1 := rfl

@[simp, to_additive]
lemma mem_one [has_one α] : a ∈ (1 : set α) ↔ a = 1 := iff.rfl

@[to_additive]
lemma one_mem_one [has_one α] : (1 : α) ∈ (1 : set α) := eq.refl _

@[simp, to_additive]
theorem one_subset [has_one α] : 1 ⊆ s ↔ (1 : α) ∈ s := singleton_subset_iff

@[to_additive]
theorem one_nonempty [has_one α] : (1 : set α).nonempty := ⟨1, rfl⟩

@[simp, to_additive]
theorem image_one [has_one α] {f : α → β} : f '' 1 = {f 1} := image_singleton

/-! ### Properties about multiplication -/

/-- The set `(s * t : set α)` is defined as `{x * y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive
/-" The set `(s + t : set α)` is defined as `{x + y | x ∈ s, y ∈ t}` in locale `pointwise`."-/]
protected def has_mul [has_mul α] : has_mul (set α) := ⟨image2 has_mul.mul⟩

localized "attribute [instance] set.has_mul set.has_add" in pointwise

@[simp, to_additive]
lemma image2_mul [has_mul α] : image2 has_mul.mul s t = s * t := rfl

@[to_additive]
lemma mem_mul [has_mul α] : a ∈ s * t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x * y = a := iff.rfl

@[to_additive]
lemma mul_mem_mul [has_mul α] (ha : a ∈ s) (hb : b ∈ t) : a * b ∈ s * t := mem_image2_of_mem ha hb

@[to_additive add_image_prod]
lemma image_mul_prod [has_mul α] : (λ x : α × α, x.fst * x.snd) '' s.prod t = s * t := image_prod _

@[simp, to_additive]
lemma image_mul_left [group α] : (λ b, a * b) '' t = (λ b, a⁻¹ * b) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[simp, to_additive]
lemma image_mul_right [group α] : (λ a, a * b) '' t = (λ a, a * b⁻¹) ⁻¹' t :=
by { rw image_eq_preimage_of_inverse; intro c; simp }

@[to_additive]
lemma image_mul_left' [group α] : (λ b, a⁻¹ * b) '' t = (λ b, a * b) ⁻¹' t := by simp

@[to_additive]
lemma image_mul_right' [group α] : (λ a, a * b⁻¹) '' t = (λ a, a * b) ⁻¹' t := by simp

@[simp, to_additive]
lemma preimage_mul_left_singleton [group α] : ((*) a) ⁻¹' {b} = {a⁻¹ * b} :=
by rw [← image_mul_left', image_singleton]

@[simp, to_additive]
lemma preimage_mul_right_singleton [group α] : (* a) ⁻¹' {b} = {b * a⁻¹} :=
by rw [← image_mul_right', image_singleton]

@[simp, to_additive]
lemma preimage_mul_left_one [group α] : (λ b, a * b) ⁻¹' 1 = {a⁻¹} :=
by rw [← image_mul_left', image_one, mul_one]

@[simp, to_additive]
lemma preimage_mul_right_one [group α] : (λ a, a * b) ⁻¹' 1 = {b⁻¹} :=
by rw [← image_mul_right', image_one, one_mul]

@[to_additive]
lemma preimage_mul_left_one' [group α] : (λ b, a⁻¹ * b) ⁻¹' 1 = {a} := by simp

@[to_additive]
lemma preimage_mul_right_one' [group α] : (λ a, a * b⁻¹) ⁻¹' 1 = {b} := by simp

@[simp, to_additive]
lemma mul_singleton [has_mul α] : s * {b} = (λ a, a * b) '' s := image2_singleton_right

@[simp, to_additive]
lemma singleton_mul [has_mul α] : {a} * t = (λ b, a * b) '' t := image2_singleton_left

@[simp, to_additive]
lemma singleton_mul_singleton [has_mul α] : ({a} : set α) * {b} = {a * b} := image2_singleton

@[to_additive]
protected lemma mul_comm [comm_semigroup α] : s * t = t * s :=
by simp only [← image2_mul, image2_swap _ s, mul_comm]

/-- `set α` is a `mul_one_class` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_zero_class` under pointwise operations if `α` is."-/]
protected def mul_one_class [mul_one_class α] : mul_one_class (set α) :=
{ mul_one := λ s, by { simp only [← singleton_one, mul_singleton, mul_one, image_id'] },
  one_mul := λ s, by { simp only [← singleton_one, singleton_mul, one_mul, image_id'] },
  ..set.has_one, ..set.has_mul }

/-- `set α` is a `semigroup` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_semigroup` under pointwise operations if `α` is. "-/]
protected def semigroup [semigroup α] : semigroup (set α) :=
{ mul_assoc := λ _ _ _, image2_assoc mul_assoc,
  ..set.has_mul }

/-- `set α` is a `monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_monoid` under pointwise operations if `α` is. "-/]
protected def monoid [monoid α] : monoid (set α) :=
{ ..set.semigroup,
  ..set.mul_one_class }

/-- `set α` is a `comm_monoid` under pointwise operations if `α` is. -/
@[to_additive /-"`set α` is an `add_comm_monoid` under pointwise operations if `α` is. "-/]
protected def comm_monoid [comm_monoid α] : comm_monoid (set α) :=
{ mul_comm := λ _ _, set.mul_comm, ..set.monoid }

localized "attribute [instance] set.mul_one_class set.add_zero_class set.semigroup set.add_semigroup
  set.monoid set.add_monoid set.comm_monoid set.add_comm_monoid" in pointwise

lemma pow_mem_pow [monoid α] (ha : a ∈ s) (n : ℕ) :
  a ^ n ∈ s ^ n :=
begin
  induction n with n ih,
  { rw pow_zero,
    exact set.mem_singleton 1 },
  { rw pow_succ,
    exact set.mul_mem_mul ha ih },
end

/-- Under `[has_mul M]`, the `singleton` map from `M` to `set M` as a `mul_hom`, that is, a map
which preserves multiplication. -/
@[to_additive "Under `[has_add A]`, the `singleton` map from `A` to `set A` as an `add_hom`,
that is, a map which preserves addition.", simps]
def singleton_mul_hom [has_mul α] : mul_hom α (set α) :=
{ to_fun := singleton,
  map_mul' := λ a b, singleton_mul_singleton.symm }

@[simp, to_additive]
lemma empty_mul [has_mul α] : ∅ * s = ∅ := image2_empty_left

@[simp, to_additive]
lemma mul_empty [has_mul α] : s * ∅ = ∅ := image2_empty_right

lemma empty_pow [monoid α] (n : ℕ) (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

instance decidable_mem_mul [monoid α] [fintype α] [decidable_eq α]
  [decidable_pred (∈ s)] [decidable_pred (∈ t)] :
  decidable_pred (∈ s * t) :=
λ _, decidable_of_iff _ mem_mul.symm

instance decidable_mem_pow [monoid α] [fintype α] [decidable_eq α]
  [decidable_pred (∈ s)] (n : ℕ) :
  decidable_pred (∈ (s ^ n)) :=
begin
  induction n with n ih,
  { simp_rw [pow_zero, mem_one], apply_instance },
  { letI := ih, rw pow_succ, apply_instance }
end

@[to_additive]
lemma mul_subset_mul [has_mul α] (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ * s₂ ⊆ t₁ * t₂ :=
image2_subset h₁ h₂

lemma pow_subset_pow [monoid α] (hst : s ⊆ t) (n : ℕ) :
  s ^ n ⊆ t ^ n :=
begin
  induction n with n ih,
  { rw pow_zero,
    exact subset.rfl },
  { rw [pow_succ, pow_succ],
    exact mul_subset_mul hst ih },
end

@[to_additive]
lemma union_mul [has_mul α] : (s ∪ t) * u = (s * u) ∪ (t * u) := image2_union_left

@[to_additive]
lemma mul_union [has_mul α] : s * (t ∪ u) = (s * t) ∪ (s * u) := image2_union_right

@[to_additive]
lemma Union_mul_left_image [has_mul α] : (⋃ a ∈ s, (λ x, a * x) '' t) = s * t :=
Union_image_left _

@[to_additive]
lemma Union_mul_right_image [has_mul α] : (⋃ a ∈ t, (λ x, x * a) '' s) = s * t :=
Union_image_right _

@[to_additive]
lemma Union_mul {ι : Sort*} [has_mul α] (s : ι → set α) (t : set α) :
  (⋃ i, s i) * t = ⋃ i, (s i * t) :=
image2_Union_left _ _ _

@[to_additive]
lemma mul_Union {ι : Sort*} [has_mul α] (t : set α) (s : ι → set α) :
  t * (⋃ i, s i) = ⋃ i, (t * s i) :=
image2_Union_right _ _ _

@[simp, to_additive]
lemma univ_mul_univ [monoid α] : (univ : set α) * univ = univ :=
begin
  have : ∀x, ∃a b : α, a * b = x := λx, ⟨x, ⟨1, mul_one x⟩⟩,
  simpa only [mem_mul, eq_univ_iff_forall, mem_univ, true_and]
end

/-- `singleton` is a monoid hom. -/
@[to_additive singleton_add_hom "singleton is an add monoid hom"]
def singleton_hom [monoid α] : α →* set α :=
{ to_fun := singleton, map_one' := rfl, map_mul' := λ a b, singleton_mul_singleton.symm }

@[to_additive]
lemma nonempty.mul [has_mul α] : s.nonempty → t.nonempty → (s * t).nonempty := nonempty.image2

@[to_additive]
lemma finite.mul [has_mul α] (hs : finite s) (ht : finite t) : finite (s * t) :=
hs.image2 _ ht

/-- multiplication preserves finiteness -/
@[to_additive "addition preserves finiteness"]
def fintype_mul [has_mul α] [decidable_eq α] (s t : set α) [hs : fintype s] [ht : fintype t] :
  fintype (s * t : set α) :=
set.fintype_image2 _ s t

@[to_additive]
lemma bdd_above_mul [ordered_comm_monoid α] {A B : set α} :
  bdd_above A → bdd_above B → bdd_above (A * B) :=
begin
  rintros ⟨bA, hbA⟩ ⟨bB, hbB⟩,
  use bA * bB,
  rintros x ⟨xa, xb, hxa, hxb, rfl⟩,
  exact mul_le_mul' (hbA hxa) (hbB hxb),
end

section big_operators
open_locale big_operators

variables {ι : Type*} [comm_monoid α]

/-- The n-ary version of `set.mem_mul`. -/
@[to_additive /-" The n-ary version of `set.mem_add`. "-/]
lemma mem_finset_prod (t : finset ι) (f : ι → set α) (a : α) :
  a ∈ ∏ i in t, f i ↔ ∃ (g : ι → α) (hg : ∀ {i}, i ∈ t → g i ∈ f i), ∏ i in t, g i = a :=
begin
  classical,
  induction t using finset.induction_on with i is hi ih generalizing a,
  { simp_rw [finset.prod_empty, set.mem_one],
    exact ⟨λ h, ⟨λ i, a, λ i, false.elim, h.symm⟩, λ ⟨f, _, hf⟩, hf.symm⟩ },
  rw [finset.prod_insert hi, set.mem_mul],
  simp_rw [finset.prod_insert hi],
  simp_rw ih,
  split,
  { rintros ⟨x, y, hx, ⟨g, hg, rfl⟩, rfl⟩,
    refine ⟨function.update g i x, λ j hj, _, _⟩,
    obtain rfl | hj := finset.mem_insert.mp hj,
    { rw function.update_same, exact hx },
    { rw update_noteq (ne_of_mem_of_not_mem hj hi), exact hg hj, },
    rw [finset.prod_update_of_not_mem hi, function.update_same], },
  { rintros ⟨g, hg, rfl⟩,
    exact ⟨g i, is.prod g, hg (is.mem_insert_self _),
      ⟨g, λ i hi, hg (finset.mem_insert_of_mem hi), rfl⟩, rfl⟩ },
end

/-- A version of `set.mem_finset_prod` with a simpler RHS for products over a fintype. -/
@[to_additive /-" A version of `set.mem_finset_sum` with a simpler RHS for sums over a fintype. "-/]
lemma mem_fintype_prod [fintype ι] (f : ι → set α) (a : α) :
  a ∈ ∏ i, f i ↔ ∃ (g : ι → α) (hg : ∀ i, g i ∈ f i), ∏ i, g i = a :=
by { rw mem_finset_prod, simp }

/-- The n-ary version of `set.mul_mem_mul`. -/
@[to_additive /-" The n-ary version of `set.add_mem_add`. "-/]
lemma finset_prod_mem_finset_prod (t : finset ι) (f : ι → set α)
  (g : ι → α) (hg : ∀ i ∈ t, g i ∈ f i) :
  ∏ i in t, g i ∈ ∏ i in t, f i :=
by { rw mem_finset_prod, exact ⟨g, hg, rfl⟩ }

/-- The n-ary version of `set.mul_subset_mul`. -/
@[to_additive /-" The n-ary version of `set.add_subset_add`. "-/]
lemma finset_prod_subset_finset_prod (t : finset ι) (f₁ f₂ : ι → set α)
  (hf : ∀ {i}, i ∈ t → f₁ i ⊆ f₂ i) :
  ∏ i in t, f₁ i ⊆ ∏ i in t, f₂ i :=
begin
  intro a,
  rw [mem_finset_prod, mem_finset_prod],
  rintro ⟨g, hg, rfl⟩,
  exact ⟨g, λ i hi, hf hi $ hg hi, rfl⟩
end

/-! TODO: define `decidable_mem_finset_prod` and `decidable_mem_finset_sum`. -/

end big_operators

/-! ### Properties about inversion -/

/-- The set `(s⁻¹ : set α)` is defined as `{x | x⁻¹ ∈ s}` in locale `pointwise`.
It is equal to `{x⁻¹ | x ∈ s}`, see `set.image_inv`. -/
@[to_additive
/-" The set `(-s : set α)` is defined as `{x | -x ∈ s}` in locale `pointwise`.
It is equal to `{-x | x ∈ s}`, see `set.image_neg`. "-/]
protected def has_inv [has_inv α] : has_inv (set α) :=
⟨preimage has_inv.inv⟩

localized "attribute [instance] set.has_inv set.has_neg" in pointwise

@[simp, to_additive]
lemma inv_empty [has_inv α] : (∅ : set α)⁻¹ = ∅ := rfl

@[simp, to_additive]
lemma inv_univ [has_inv α] : (univ : set α)⁻¹ = univ := rfl

@[simp, to_additive]
lemma nonempty_inv [group α] {s : set α} : s⁻¹.nonempty ↔ s.nonempty :=
inv_involutive.surjective.nonempty_preimage

@[to_additive] lemma nonempty.inv [group α] {s : set α} (h : s.nonempty) : s⁻¹.nonempty :=
nonempty_inv.2 h

@[simp, to_additive]
lemma mem_inv [has_inv α] : a ∈ s⁻¹ ↔ a⁻¹ ∈ s := iff.rfl

@[to_additive]
lemma inv_mem_inv [group α] : a⁻¹ ∈ s⁻¹ ↔ a ∈ s :=
by simp only [mem_inv, inv_inv]

@[simp, to_additive]
lemma inv_preimage [has_inv α] : has_inv.inv ⁻¹' s = s⁻¹ := rfl

@[simp, to_additive]
lemma image_inv [group α] : has_inv.inv '' s = s⁻¹ :=
by { simp only [← inv_preimage], rw [image_eq_preimage_of_inverse]; intro; simp only [inv_inv] }

@[simp, to_additive]
lemma inter_inv [has_inv α] : (s ∩ t)⁻¹ = s⁻¹ ∩ t⁻¹ := preimage_inter

@[simp, to_additive]
lemma union_inv [has_inv α] : (s ∪ t)⁻¹ = s⁻¹ ∪ t⁻¹ := preimage_union

@[simp, to_additive]
lemma compl_inv [has_inv α] : (sᶜ)⁻¹ = (s⁻¹)ᶜ := preimage_compl

@[simp, to_additive]
protected lemma inv_inv [group α] : s⁻¹⁻¹ = s :=
by { simp only [← inv_preimage, preimage_preimage, inv_inv, preimage_id'] }

@[simp, to_additive]
protected lemma univ_inv [group α] : (univ : set α)⁻¹ = univ := preimage_univ

@[simp, to_additive]
lemma inv_subset_inv [group α] {s t : set α} : s⁻¹ ⊆ t⁻¹ ↔ s ⊆ t :=
(equiv.inv α).surjective.preimage_subset_preimage_iff

@[to_additive] lemma inv_subset [group α] {s t : set α} : s⁻¹ ⊆ t ↔ s ⊆ t⁻¹ :=
by { rw [← inv_subset_inv, set.inv_inv] }

@[to_additive] lemma finite.inv [group α] {s : set α} (hs : finite s) : finite s⁻¹ :=
hs.preimage $ inv_injective.inj_on _

@[to_additive] lemma inv_singleton {β : Type*} [group β] (x : β) : ({x} : set β)⁻¹ = {x⁻¹} :=
by { ext1 y, rw [mem_inv, mem_singleton_iff, mem_singleton_iff, inv_eq_iff_inv_eq, eq_comm], }

/-! ### Properties about scalar multiplication -/

/-- The scaling of a set `(x • s : set β)` by a scalar `x ∶ α` is defined as `{x • y | y ∈ s}`
in locale `pointwise`. -/
@[to_additive has_vadd_set "The translation of a set `(x +ᵥ s : set β)` by a scalar `x ∶ α` is
defined as `{x +ᵥ y | y ∈ s}` in locale `pointwise`."]
protected def has_scalar_set [has_scalar α β] : has_scalar α (set β) :=
⟨λ a, image (has_scalar.smul a)⟩

/-- The pointwise scalar multiplication `(s • t : set β)` by a set of scalars `s ∶ set α`
is defined as `{x • y | x ∈ s, y ∈ t}` in locale `pointwise`. -/
@[to_additive has_vadd "The pointwise translation `(s +ᵥ t : set β)` by a set of constants
`s ∶ set α` is defined as `{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def has_scalar [has_scalar α β] : has_scalar (set α) (set β) :=
⟨image2 has_scalar.smul⟩

localized "attribute [instance] set.has_scalar_set set.has_scalar" in pointwise
localized "attribute [instance] set.has_vadd_set set.has_vadd" in pointwise

@[simp, to_additive]
lemma image_smul [has_scalar α β] {t : set β} : (λ x, a • x) '' t = a • t := rfl

@[to_additive]
lemma mem_smul_set [has_scalar α β] {t : set β} : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

@[to_additive]
lemma smul_mem_smul_set [has_scalar α β] {t : set β} (hy : y ∈ t) : a • y ∈ a • t :=
⟨y, hy, rfl⟩

@[to_additive]
lemma smul_set_union [has_scalar α β] {s t : set β} : a • (s ∪ t) = a • s ∪ a • t :=
by simp only [← image_smul, image_union]

@[to_additive]
lemma smul_set_inter [group α] [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
(image_inter $ mul_action.injective a).symm

lemma smul_set_inter₀ [group_with_zero α] [mul_action α β] {s t : set β} (ha : a ≠ 0) :
  a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

@[to_additive]
lemma smul_set_inter_subset [has_scalar α β] {s t : set β} :
  a • (s ∩ t) ⊆ a • s ∩ a • t := image_inter_subset _ _ _

@[simp, to_additive]
lemma smul_set_empty [has_scalar α β] (a : α) : a • (∅ : set β) = ∅ :=
by rw [← image_smul, image_empty]

@[to_additive]
lemma smul_set_mono [has_scalar α β] {s t : set β} (h : s ⊆ t) : a • s ⊆ a • t :=
by { simp only [← image_smul, image_subset, h] }

@[simp, to_additive]
lemma image2_smul [has_scalar α β] {t : set β} : image2 has_scalar.smul s t = s • t := rfl

@[to_additive]
lemma mem_smul [has_scalar α β] {t : set β} : x ∈ s • t ↔ ∃ a y, a ∈ s ∧ y ∈ t ∧ a • y = x :=
iff.rfl

lemma mem_smul_of_mem [has_scalar α β] {t : set β} {a} {b} (ha : a ∈ s) (hb : b ∈ t) :
  a • b ∈ s • t :=
⟨a, b, ha, hb, rfl⟩

@[to_additive]
lemma image_smul_prod [has_scalar α β] {t : set β} :
  (λ x : α × β, x.fst • x.snd) '' s.prod t = s • t :=
image_prod _

@[to_additive]
theorem range_smul_range [has_scalar α β] {ι κ : Type*} (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ hx, let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := set.mem_smul.1 hx in
  ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
λ ⟨⟨i, j⟩, h⟩, set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[simp, to_additive]
lemma singleton_smul [has_scalar α β] {t : set β} : ({a} : set α) • t = a • t :=
image2_singleton_left

@[to_additive]
instance smul_comm_class_set {γ : Type*}
  [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class α (set β) (set γ) :=
{ smul_comm := λ a T T',
    by simp only [←image2_smul, ←image_smul, image2_image_right, image_image2, smul_comm] }

@[to_additive]
instance smul_comm_class_set' {γ : Type*}
  [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) β (set γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class {γ : Type*}
  [has_scalar α γ] [has_scalar β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) (set β) (set γ) :=
{ smul_comm := λ T T' T'', begin
    simp only [←image2_smul, image2_swap _ T],
    exact image2_assoc (λ b c a, smul_comm a b c),
  end }

instance is_scalar_tower {γ : Type*}
  [has_scalar α β] [has_scalar α γ] [has_scalar β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (set γ) :=
{ smul_assoc := λ a b T, by simp only [←image_smul, image_image, smul_assoc] }

instance is_scalar_tower' {γ : Type*}
  [has_scalar α β] [has_scalar α γ] [has_scalar β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (set β) (set γ) :=
{ smul_assoc := λ a T T',
    by simp only [←image_smul, ←image2_smul, image_image2, image2_image_left, smul_assoc] }

instance is_scalar_tower'' {γ : Type*}
  [has_scalar α β] [has_scalar α γ] [has_scalar β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (set α) (set β) (set γ) :=
{ smul_assoc := λ T T' T'', image2_assoc smul_assoc }

section monoid

/-! ### `set α` as a `(∪,*)`-semiring -/

/-- An alias for `set α`, which has a semiring structure given by `∪` as "addition" and pointwise
  multiplication `*` as "multiplication". -/
@[derive inhabited] def set_semiring (α : Type*) : Type* := set α

/-- The identitiy function `set α → set_semiring α`. -/
protected def up (s : set α) : set_semiring α := s
/-- The identitiy function `set_semiring α → set α`. -/
protected def set_semiring.down (s : set_semiring α) : set α := s
@[simp] protected lemma down_up {s : set α} : s.up.down = s := rfl
@[simp] protected lemma up_down {s : set_semiring α} : s.down.up = s := rfl

instance set_semiring.add_comm_monoid : add_comm_monoid (set_semiring α) :=
{ add := λ s t, (s ∪ t : set α),
  zero := (∅ : set α),
  add_assoc := union_assoc,
  zero_add := empty_union,
  add_zero := union_empty,
  add_comm := union_comm, }

instance set_semiring.non_unital_non_assoc_semiring [has_mul α] :
  non_unital_non_assoc_semiring (set_semiring α) :=
{ zero_mul := λ s, empty_mul,
  mul_zero := λ s, mul_empty,
  left_distrib := λ _ _ _, mul_union,
  right_distrib := λ _ _ _, union_mul,
  ..set.has_mul, ..set_semiring.add_comm_monoid }

instance set_semiring.non_assoc_semiring [mul_one_class α] : non_assoc_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_non_assoc_semiring, ..set.mul_one_class }

instance set_semiring.non_unital_semiring [semigroup α] : non_unital_semiring (set_semiring α) :=
{ ..set_semiring.non_unital_non_assoc_semiring, ..set.semigroup }

instance set_semiring.semiring [monoid α] : semiring (set_semiring α) :=
{ ..set_semiring.non_assoc_semiring, ..set_semiring.non_unital_semiring }

instance set_semiring.comm_semiring [comm_monoid α] : comm_semiring (set_semiring α) :=
{ ..set.comm_monoid, ..set_semiring.semiring }

/-- A multiplicative action of a monoid on a type β gives also a
 multiplicative action on the subsets of β. -/
@[to_additive "An additive action of an additive monoid on a type β gives also an additive action
on the subsets of β."]
protected def mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, image_eta, one_smul, image_id'] },
  ..set.has_scalar_set }

localized "attribute [instance] set.mul_action_set set.add_action_set" in pointwise

section mul_hom

variables [has_mul α] [has_mul β] (m : mul_hom α β)

@[to_additive]
lemma image_mul : m '' (s * t) = m '' s * m '' t :=
by { simp only [← image2_mul, image_image2, image2_image_left, image2_image_right, m.map_mul] }

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintros _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (m.map_mul _ _).symm ⟩ }

end mul_hom

/-- The image of a set under function is a ring homomorphism
with respect to the pointwise operations on sets. -/
def image_hom [monoid α] [monoid β] (f : α →* β) : set_semiring α →+* set_semiring β :=
{ to_fun := image f,
  map_zero' := image_empty _,
  map_one' := by simp only [← singleton_one, image_singleton, f.map_one],
  map_add' := image_union _,
  map_mul' := λ _ _, image_mul f.to_mul_hom }

end monoid

end set

open set
open_locale pointwise

section

variables {α : Type*} {β : Type*}

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_set [has_zero α] [has_zero β] [smul_with_zero α β] {s : set β} (h : s.nonempty) :
  (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

section group
variables [group α] [mul_action α β]

@[simp, to_additive]
lemma smul_mem_smul_set_iff {a : α} {A : set β} {x : β} : a • x ∈ a • A ↔ x ∈ A :=
⟨λ h, begin
  rw [←inv_smul_smul a x, ←inv_smul_smul a A],
  exact smul_mem_smul_set h,
end, smul_mem_smul_set⟩

@[to_additive]
lemma mem_smul_set_iff_inv_smul_mem {a : α} {A : set β} {x : β} : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show x ∈ mul_action.to_perm a '' A ↔ _, from mem_image_equiv

@[to_additive]
lemma mem_inv_smul_set_iff {a : α} {A : set β} {x : β} : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
lemma preimage_smul (a : α) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
((mul_action.to_perm a).symm.image_eq_preimage _).symm

@[to_additive]
lemma preimage_smul_inv (a : α) (t : set β) : (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul (to_units a)⁻¹ t

@[simp, to_additive]
lemma set_smul_subset_set_smul_iff {a : α} {A B : set β} : a • A ⊆ a • B ↔ A ⊆ B :=
image_subset_image_iff $ mul_action.injective _

@[to_additive]
lemma set_smul_subset_iff {a : α} {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
(image_subset_iff).trans $ iff_of_eq $ congr_arg _ $
  preimage_equiv_eq_image_symm _ $ mul_action.to_perm _

@[to_additive]
lemma subset_set_smul_iff {a : α} {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
iff.symm $ (image_subset_iff).trans $ iff.symm $ iff_of_eq $ congr_arg _ $
  image_equiv_eq_preimage_symm _ $ mul_action.to_perm _

end group

section group_with_zero
variables [group_with_zero α] [mul_action α β]

@[simp] lemma smul_mem_smul_set_iff₀ {a : α} (ha : a ≠ 0) (A : set β)
  (x : β) : a • x ∈ a • A ↔ x ∈ A :=
show units.mk0 a ha • _ ∈ _ ↔ _, from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show _ ∈ units.mk0 a ha • _ ↔ _, from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ {a : α} (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_set_iff

lemma preimage_smul₀ {a : α} (ha : a ≠ 0) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
preimage_smul (units.mk0 a ha) t

lemma preimage_smul_inv₀ {a : α} (ha : a ≠ 0) (t : set β) :
  (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul ((units.mk0 a ha)⁻¹) t

@[simp] lemma set_smul_subset_set_smul_iff₀ {a : α} (ha : a ≠ 0) {A B : set β} :
  a • A ⊆ a • B ↔ A ⊆ B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_set_smul_iff

lemma set_smul_subset_iff₀ {a : α} (ha : a ≠ 0) {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_iff

lemma subset_set_smul_iff₀ {a : α} (ha : a ≠ 0) {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_set_smul_iff

end group_with_zero

end

namespace finset

variables {α : Type*} [decidable_eq α]

/-- The pointwise product of two finite sets `s` and `t`:
`st = s ⬝ t = s * t = { x * y | x ∈ s, y ∈ t }`. -/
@[to_additive /-"The pointwise sum of two finite sets `s` and `t`:
`s + t = { x + y | x ∈ s, y ∈ t }`. "-/]
protected def has_mul [has_mul α] : has_mul (finset α) :=
⟨λ s t, (s.product t).image (λ p : α × α, p.1 * p.2)⟩

localized "attribute [instance] finset.has_mul finset.has_add" in pointwise

@[to_additive]
lemma mul_def [has_mul α] {s t : finset α} :
  s * t = (s.product t).image (λ p : α × α, p.1 * p.2) := rfl

@[to_additive]
lemma mem_mul [has_mul α] {s t : finset α} {x : α} :
  x ∈ s * t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
by { simp only [finset.mul_def, and.assoc, mem_image, exists_prop, prod.exists, mem_product] }

@[simp, norm_cast, to_additive]
lemma coe_mul [has_mul α] {s t : finset α} : (↑(s * t) : set α) = ↑s * ↑t :=
by { ext, simp only [mem_mul, set.mem_mul, mem_coe] }

@[to_additive]
lemma mul_mem_mul [has_mul α] {s t : finset α} {x y : α} (hx : x ∈ s) (hy : y ∈ t) :
  x * y ∈ s * t :=
by { simp only [finset.mem_mul], exact ⟨x, y, hx, hy, rfl⟩ }

@[to_additive]
lemma mul_card_le [has_mul α] {s t : finset α} : (s * t).card ≤ s.card * t.card :=
by { convert finset.card_image_le, rw [finset.card_product, mul_comm] }

open_locale classical

/-- A finite set `U` contained in the product of two sets `S * S'` is also contained in the product
of two finite sets `T * T' ⊆ S * S'`. -/
@[to_additive]
lemma subset_mul {M : Type*} [monoid M] {S : set M} {S' : set M} {U : finset M} (f : ↑U ⊆ S * S') :
  ∃ (T T' : finset M), ↑T ⊆ S ∧ ↑T' ⊆ S' ∧ U ⊆ T * T' :=
begin
  apply finset.induction_on' U,
  { use [∅, ∅], simp only [finset.empty_subset, finset.coe_empty, set.empty_subset, and_self], },
  rintros a s haU hs has ⟨T, T', hS, hS', h⟩,
  obtain ⟨x, y, hx, hy, ha⟩ := set.mem_mul.1 (f haU),
  use [insert x T, insert y T'],
  simp only [finset.coe_insert],
  repeat { rw [set.insert_subset], },
  use [hx, hS, hy, hS'],
  refine finset.insert_subset.mpr ⟨_, _⟩,
  { rw finset.mem_mul,
    use [x,y],
    simpa only [true_and, true_or, eq_self_iff_true, finset.mem_insert], },
  { suffices g : (s : set M) ⊆ insert x T * insert y T', { norm_cast at g, assumption, },
    transitivity ↑(T * T'),
    apply h,
    rw finset.coe_mul,
    apply set.mul_subset_mul (set.subset_insert x T) (set.subset_insert y T'), },
end

end finset

/-! Some lemmas about pointwise multiplication and submonoids. Ideally we put these in
  `group_theory.submonoid.basic`, but currently we cannot because that file is imported by this. -/
namespace submonoid

variables {M : Type*} [monoid M]

@[to_additive]
lemma mul_subset {s t : set M} {S : submonoid M} (hs : s ⊆ S) (ht : t ⊆ S) : s * t ⊆ S :=
by { rintro _ ⟨p, q, hp, hq, rfl⟩, exact submonoid.mul_mem _ (hs hp) (ht hq) }

@[to_additive]
lemma mul_subset_closure {s t u : set M} (hs : s ⊆ u) (ht : t ⊆ u) :
  s * t ⊆ submonoid.closure u :=
mul_subset (subset.trans hs submonoid.subset_closure) (subset.trans ht submonoid.subset_closure)

@[to_additive]
lemma coe_mul_self_eq (s : submonoid M) : (s : set M) * s = s :=
begin
  ext x,
  refine ⟨_, λ h, ⟨x, 1, h, s.one_mem, mul_one x⟩⟩,
  rintros ⟨a, b, ha, hb, rfl⟩,
  exact s.mul_mem ha hb
end

@[to_additive]
lemma closure_mul_le (S T : set M) : closure (S * T) ≤ closure S ⊔ closure T :=
Inf_le $ λ x ⟨s, t, hs, ht, hx⟩, hx ▸ (closure S ⊔ closure T).mul_mem
    (set_like.le_def.mp le_sup_left $ subset_closure hs)
    (set_like.le_def.mp le_sup_right $ subset_closure ht)

@[to_additive]
lemma sup_eq_closure (H K : submonoid M) : H ⊔ K = closure (H * K) :=
le_antisymm
  (sup_le
    (λ h hh, subset_closure ⟨h, 1, hh, K.one_mem, mul_one h⟩)
    (λ k hk, subset_closure ⟨1, k, H.one_mem, hk, one_mul k⟩))
  (by conv_rhs { rw [← closure_eq H, ← closure_eq K] }; apply closure_mul_le)

end submonoid

namespace group

lemma card_pow_eq_card_pow_card_univ_aux {f : ℕ → ℕ} (h1 : monotone f)
  {B : ℕ} (h2 : ∀ n, f n ≤ B) (h3 : ∀ n, f n = f (n + 1) → f (n + 1) = f (n + 2)) :
  ∀ k, B ≤ k → f k = f B :=
begin
  have key : ∃ n : ℕ, n ≤ B ∧ f n = f (n + 1),
  { contrapose! h2,
    suffices : ∀ n : ℕ, n ≤ B + 1 → n ≤ f n,
    { exact ⟨B + 1, this (B + 1) (le_refl (B + 1))⟩ },
    exact λ n, nat.rec (λ h, nat.zero_le (f 0)) (λ n ih h, lt_of_le_of_lt (ih (n.le_succ.trans h))
      (lt_of_le_of_ne (h1 n.le_succ) (h2 n (nat.succ_le_succ_iff.mp h)))) n },
  { obtain ⟨n, hn1, hn2⟩ := key,
    replace key : ∀ k : ℕ, f (n + k) = f (n + k + 1) ∧ f (n + k) = f n :=
    λ k, nat.rec ⟨hn2, rfl⟩ (λ k ih, ⟨h3 _ ih.1, ih.1.symm.trans ih.2⟩) k,
    replace key : ∀ k : ℕ, n ≤ k → f k = f n :=
    λ k hk, (congr_arg f (add_tsub_cancel_of_le hk)).symm.trans (key (k - n)).2,
    exact λ k hk, (key k (hn1.trans hk)).trans (key B hn1).symm },
end

variables {G : Type*} [group G] [fintype G] (S : set G)

lemma card_pow_eq_card_pow_card_univ [∀ (k : ℕ), decidable_pred (∈ (S ^ k))] :
  ∀ k, fintype.card G ≤ k → fintype.card ↥(S ^ k) = fintype.card ↥(S ^ (fintype.card G)) :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr ⟨1⟩,
  by_cases hS : S = ∅,
  { intros k hk,
    congr' 2,
    rw [hS, empty_pow _ (ne_of_gt (lt_of_lt_of_le hG hk)), empty_pow _ (ne_of_gt hG)] },
  obtain ⟨a, ha⟩ := set.ne_empty_iff_nonempty.mp hS,
  classical,
  have key : ∀ a (s t : set G), (∀ b : G, b ∈ s → a * b ∈ t) → fintype.card s ≤ fintype.card t,
  { refine λ a s t h, fintype.card_le_of_injective (λ ⟨b, hb⟩, ⟨a * b, h b hb⟩) _,
    rintros ⟨b, hb⟩ ⟨c, hc⟩ hbc,
    exact subtype.ext (mul_left_cancel (subtype.ext_iff.mp hbc)) },
  have mono : monotone (λ n, fintype.card ↥(S ^ n) : ℕ → ℕ) :=
  monotone_nat_of_le_succ (λ n, key a _ _ (λ b hb, set.mul_mem_mul ha hb)),
  convert card_pow_eq_card_pow_card_univ_aux mono (λ n, set_fintype_card_le_univ (S ^ n))
    (λ n h, le_antisymm (mono (n + 1).le_succ) (key a⁻¹ _ _ _)),
  { simp only [finset.filter_congr_decidable, fintype.card_of_finset] },
  replace h : {a} * S ^ n = S ^ (n + 1),
  { refine set.eq_of_subset_of_card_le _ (le_trans (ge_of_eq h) _),
    { exact mul_subset_mul (set.singleton_subset_iff.mpr ha) set.subset.rfl },
    { convert key a (S ^ n) ({a} * S ^ n) (λ b hb, set.mul_mem_mul (set.mem_singleton a) hb) } },
  rw [pow_succ', ←h, mul_assoc, ←pow_succ', h],
  rintros _ ⟨b, c, hb, hc, rfl⟩,
  rwa [set.mem_singleton_iff.mp hb, inv_mul_cancel_left],
end

end group
