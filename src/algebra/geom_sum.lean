/-
Copyright (c) 2019 Neil Strickland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Neil Strickland
-/

import algebra.group_with_zero.power
import algebra.big_operators.order
import algebra.big_operators.ring
import algebra.big_operators.intervals
import tactic.abel

/-!
# Partial sums of geometric series

This file determines the values of the geometric series $\sum_{i=0}^{n-1} x^i$ and
$\sum_{i=0}^{n-1} x^i y^{n-1-i}$ and variants thereof. We also provide some bounds on the
"geometric" sum of `a/b^i` where `a b : ℕ`.

## Main definitions

* `geom_sum` defines for each $x$ in a semiring and each natural number $n$ the partial sum
  $\sum_{i=0}^{n-1} x^i$ of the geometric series.
* `geom_sum₂` defines for each $x,y$ in a semiring and each natural number $n$ the partial sum
  $\sum_{i=0}^{n-1} x^i y^{n-1-i}$ of the geometric series.

## Main statements

* `geom_sum_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-x^m}{x-1}$ in a division ring.
* `geom_sum₂_Ico` proves that $\sum_{i=m}^{n-1} x^i=\frac{x^n-y^{n-m}x^m}{x-y}$ in a field.

Several variants are recorded, generalising in particular to the case of a noncommutative ring in
which `x` and `y` commute. Even versions not using division or subtraction, valid in each semiring,
are recorded.
-/

universe u
variable {α : Type u}

open finset opposite

open_locale big_operators

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i$. -/
def geom_sum [semiring α] (x : α) (n : ℕ) :=
∑ i in range n, x ^ i

theorem geom_sum_def [semiring α] (x : α) (n : ℕ) :
  geom_sum x n = ∑ i in range n, x ^ i := rfl

@[simp] theorem geom_sum_zero [semiring α] (x : α) :
  geom_sum x 0 = 0 := rfl

@[simp] theorem geom_sum_one [semiring α] (x : α) :
  geom_sum x 1 = 1 :=
by { rw [geom_sum_def, sum_range_one, pow_zero] }

@[simp] lemma op_geom_sum [ring α] (x : α) (n : ℕ) :
  op (geom_sum x n) = geom_sum (op x) n :=
by simp [geom_sum_def]

/-- Sum of the finite geometric series $\sum_{i=0}^{n-1} x^i y^{n-1-i}$. -/
def geom_sum₂ [semiring α] (x y : α) (n : ℕ) :=
∑ i in range n, x ^ i * (y ^ (n - 1 - i))

theorem geom_sum₂_def [semiring α] (x y : α) (n : ℕ) :
  geom_sum₂ x y n = ∑ i in range n, x ^ i * y ^ (n - 1 - i) := rfl

@[simp] theorem geom_sum₂_zero [semiring α] (x y : α) :
  geom_sum₂ x y 0 = 0 := rfl

@[simp] theorem geom_sum₂_one [semiring α] (x y : α) :
  geom_sum₂ x y 1 = 1 :=
by { have : 1 - 1 - 0 = 0 := rfl,
     rw [geom_sum₂_def, sum_range_one, this, pow_zero, pow_zero, mul_one] }

@[simp] lemma op_geom_sum₂ [ring α] (x y : α) (n : ℕ) :
  op (geom_sum₂ x y n) = geom_sum₂ (op y) (op x) n :=
begin
  simp only [geom_sum₂_def, op_sum, op_mul, op_pow],
  rw ← sum_range_reflect,
  refine sum_congr rfl (λ j j_in, _),
  rw [mem_range, nat.lt_iff_add_one_le] at j_in,
  congr,
  apply tsub_tsub_cancel_of_le,
  exact le_tsub_of_add_le_right j_in
end

@[simp] theorem geom_sum₂_with_one [semiring α] (x : α) (n : ℕ) :
  geom_sum₂ x 1 n = geom_sum x n :=
sum_congr rfl (λ i _, by { rw [one_pow, mul_one] })

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
protected theorem commute.geom_sum₂_mul_add [semiring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_sum₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
begin
  let f := λ (m i : ℕ), (x + y) ^ i * y ^ (m - 1 - i),
  change (∑ i in range n, (f n) i) * x + y ^ n = (x + y) ^ n,
  induction n with n ih,
  { rw [range_zero, sum_empty, zero_mul, zero_add, pow_zero, pow_zero] },
  { have f_last : f (n + 1) n = (x + y) ^ n :=
     by { dsimp [f],
          rw [← tsub_add_eq_tsub_tsub, nat.add_comm, tsub_self, pow_zero, mul_one] },
    have f_succ : ∀ i, i ∈ range n → f (n + 1) i = y * f n i :=
      λ i hi, by {
        dsimp [f],
        have : commute y ((x + y) ^ i) :=
         (h.symm.add_right (commute.refl y)).pow_right i,
        rw [← mul_assoc, this.eq, mul_assoc, ← pow_succ y (n - 1 - i)],
        congr' 2,
        rw [add_tsub_cancel_right, ← tsub_add_eq_tsub_tsub, add_comm 1 i],
        have : i + 1 + (n - (i + 1)) = n := add_tsub_cancel_of_le (mem_range.mp hi),
        rw [add_comm (i + 1)] at this,
        rw [← this, add_tsub_cancel_right, add_comm i 1, ← add_assoc,
            add_tsub_cancel_right] },
    rw [pow_succ (x + y), add_mul, sum_range_succ_comm, add_mul, f_last, add_assoc],
    rw (((commute.refl x).add_right h).pow_right n).eq,
    congr' 1,
    rw [sum_congr rfl f_succ, ← mul_sum, pow_succ y, mul_assoc, ← mul_add y, ih] }
end

theorem geom_sum₂_self {α : Type*} [comm_ring α] (x : α) (n : ℕ) :
  geom_sum₂ x x n = n * x ^ (n-1) :=
calc  ∑ i in finset.range n, x ^ i * x ^ (n - 1 - i)
    = ∑ i in finset.range n, x ^ (i + (n - 1 - i)) : by simp_rw [← pow_add]
... = ∑ i in finset.range n, x ^ (n - 1) : finset.sum_congr rfl
  (λ i hi, congr_arg _ $ add_tsub_cancel_of_le $ nat.le_pred_of_lt $ finset.mem_range.1 hi)
... = (finset.range n).card • (x ^ (n - 1)) : finset.sum_const _
... = n * x ^ (n - 1) : by rw [finset.card_range, nsmul_eq_mul]

/-- $x^n-y^n = (x-y) \sum x^ky^{n-1-k}$ reformulated without `-` signs. -/
theorem geom_sum₂_mul_add [comm_semiring α] (x y : α) (n : ℕ) :
  (geom_sum₂ (x + y) y n) * x + y ^ n = (x + y) ^ n :=
(commute.all x y).geom_sum₂_mul_add n

theorem geom_sum_mul_add [semiring α] (x : α) (n : ℕ) :
  (geom_sum (x + 1) n) * x + 1 = (x + 1) ^ n :=
begin
  have := (commute.one_right x).geom_sum₂_mul_add n,
  rw [one_pow, geom_sum₂_with_one] at this,
  exact this
end

protected theorem commute.geom_sum₂_mul [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (geom_sum₂ x y n) * (x - y) = x ^ n - y ^ n :=
begin
  have := (h.sub_left (commute.refl y)).geom_sum₂_mul_add n,
  rw [sub_add_cancel] at this,
  rw [← this, add_sub_cancel]
end

lemma commute.mul_neg_geom_sum₂ [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (y - x) * (geom_sum₂ x y n) = y ^ n - x ^ n :=
begin
  rw ← op_inj_iff,
  simp only [op_mul, op_sub, op_geom_sum₂, op_pow],
  exact (commute.op h.symm).geom_sum₂_mul n
end

lemma commute.mul_geom_sum₂ [ring α] {x y : α} (h : commute x y) (n : ℕ) :
  (x - y) * (geom_sum₂ x y n) = x ^ n - y ^ n :=
by rw [← neg_sub (y ^ n), ← h.mul_neg_geom_sum₂, ← neg_mul_eq_neg_mul_symm, neg_sub]

theorem geom_sum₂_mul [comm_ring α] (x y : α) (n : ℕ) :
  (geom_sum₂ x y n) * (x - y) = x ^ n - y ^ n :=
(commute.all x y).geom_sum₂_mul n

theorem geom_sum_mul [ring α] (x : α) (n : ℕ) :
  (geom_sum x n) * (x - 1) = x ^ n - 1 :=
begin
  have := (commute.one_right x).geom_sum₂_mul n,
  rw [one_pow, geom_sum₂_with_one] at this,
  exact this
end

lemma mul_geom_sum [ring α] (x : α) (n : ℕ) :
  (x - 1) * (geom_sum x n) = x ^ n - 1 :=
begin
  rw ← op_inj_iff,
  simpa using geom_sum_mul (op x) n,
end

theorem geom_sum_mul_neg [ring α] (x : α) (n : ℕ) :
  (geom_sum x n) * (1 - x) = 1 - x ^ n :=
begin
  have := congr_arg has_neg.neg (geom_sum_mul x n),
  rw [neg_sub, ← mul_neg_eq_neg_mul_symm, neg_sub] at this,
  exact this
end

lemma mul_neg_geom_sum [ring α] (x : α) (n : ℕ) :
  (1 - x) * (geom_sum x n) = 1 - x ^ n :=
begin
  rw ← op_inj_iff,
  simpa using geom_sum_mul_neg (op x) n,
end

protected theorem commute.geom_sum₂ [division_ring α] {x y : α} (h' : commute x y) (h : x ≠ y)
  (n : ℕ) : (geom_sum₂ x y n) = (x ^ n - y ^ n) / (x - y) :=
have x - y ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← h'.geom_sum₂_mul, mul_div_cancel _ this]

theorem geom₂_sum [field α] {x y : α} (h : x ≠ y) (n : ℕ) :
  (geom_sum₂ x y n) = (x ^ n - y ^ n) / (x - y) :=
(commute.all x y).geom_sum₂ h n

theorem geom_sum_eq [division_ring α] {x : α} (h : x ≠ 1) (n : ℕ) :
  (geom_sum x n) = (x ^ n - 1) / (x - 1) :=
have x - 1 ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← geom_sum_mul, mul_div_cancel _ this]

protected theorem commute.mul_geom_sum₂_Ico [ring α] {x y : α} (h : commute x y) {m n : ℕ}
  (hmn : m ≤ n) :
  (x - y) * (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
begin
  rw [sum_Ico_eq_sub _ hmn, ← geom_sum₂_def],
  have : ∑ k in range m, x ^ k * y ^ (n - 1 - k)
    = ∑ k in range m, x ^ k * (y ^ (n - m) * y ^ (m - 1 - k)),
    { refine sum_congr rfl (λ j j_in, _),
      rw ← pow_add,
      congr,
      rw [mem_range, nat.lt_iff_add_one_le, add_comm] at j_in,
      have h' : n - m + (m - (1 + j)) = n - (1 + j) := tsub_add_tsub_cancel hmn j_in,
      rw [← tsub_add_eq_tsub_tsub m, h', ← tsub_add_eq_tsub_tsub] },
  rw this,
  simp_rw pow_mul_comm y (n-m) _,
  simp_rw ← mul_assoc,
  rw [← sum_mul, ← geom_sum₂_def, mul_sub, h.mul_geom_sum₂, ← mul_assoc,
    h.mul_geom_sum₂, sub_mul, ← pow_add, add_tsub_cancel_of_le hmn,
    sub_sub_sub_cancel_right (x ^ n) (x ^ m * y ^ (n - m)) (y ^ n)],
end

protected theorem commute.geom_sum₂_succ_eq {α : Type u} [ring α] {x y : α}
  (h : commute x y) {n : ℕ} :
  geom_sum₂ x y (n + 1) = x ^ n + y * (geom_sum₂ x y n) :=
begin
  simp_rw [geom_sum₂, mul_sum, sum_range_succ_comm, nat.add_succ_sub_one, add_zero, tsub_self,
    pow_zero, mul_one, add_right_inj, ←mul_assoc, (h.symm.pow_right _).eq, mul_assoc, ←pow_succ],
  refine sum_congr rfl (λ i hi, _),
  suffices : n - 1 - i + 1 = n - i, { rw this },
  cases n,
  { exact absurd (list.mem_range.mp hi) i.not_lt_zero },
  { rw [tsub_add_eq_add_tsub (nat.le_pred_of_lt (list.mem_range.mp hi)),
        tsub_add_cancel_of_le (nat.succ_le_iff.mpr n.succ_pos)] },
end

theorem geom_sum₂_succ_eq {α : Type u} [comm_ring α] (x y : α)  {n : ℕ} :
  geom_sum₂ x y (n + 1) = x ^ n + y * (geom_sum₂ x y n) :=
(commute.all x y).geom_sum₂_succ_eq

theorem mul_geom_sum₂_Ico [comm_ring α] (x y : α) {m n : ℕ} (hmn : m ≤ n) :
  (x - y) * (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) = x ^ n - x ^ m * y ^ (n - m) :=
(commute.all x y).mul_geom_sum₂_Ico hmn

protected theorem commute.geom_sum₂_Ico_mul [ring α] {x y : α} (h : commute x y) {m n : ℕ}
  (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i)) * (x - y) = x ^ n -  y ^ (n - m) * x ^ m :=
begin
  rw ← op_inj_iff,
  simp only [op_sub, op_mul, op_pow, op_sum],
  have : ∑ k in Ico m n, op y ^ (n - 1 - k) * op x ^ k
    = ∑ k in Ico m n, op x ^ k * op y ^ (n - 1 - k),
  { refine sum_congr rfl (λ k k_in, _),
    apply commute.pow_pow (commute.op h.symm) },
  rw this,
  exact (commute.op h).mul_geom_sum₂_Ico hmn
end

theorem geom_sum_Ico_mul [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (x - 1) = x^n - x^m :=
by rw [sum_Ico_eq_sub _ hmn, ← geom_sum_def, ← geom_sum_def, sub_mul,
  geom_sum_mul, geom_sum_mul, sub_sub_sub_cancel_right]

theorem geom_sum_Ico_mul_neg [ring α] (x : α) {m n : ℕ} (hmn : m ≤ n) :
  (∑ i in finset.Ico m n, x ^ i) * (1 - x) = x^m - x^n :=
by rw [sum_Ico_eq_sub _ hmn, ← geom_sum_def, ← geom_sum_def, sub_mul,
  geom_sum_mul_neg, geom_sum_mul_neg, sub_sub_sub_cancel_left]

protected theorem commute.geom_sum₂_Ico [division_ring α] {x y : α} (h : commute x y) (hxy : x ≠ y)
  {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m ) / (x - y) :=
have x - y ≠ 0, by simp [*, -sub_eq_add_neg, sub_eq_iff_eq_add] at *,
by rw [← h.geom_sum₂_Ico_mul hmn, mul_div_cancel _ this]

theorem geom_sum₂_Ico [field α] {x y : α} (hxy : x ≠ y) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i * y ^ (n - 1 - i) = (x ^ n - y ^ (n - m) * x ^ m ) / (x - y) :=
(commute.all x y).geom_sum₂_Ico hxy hmn

theorem geom_sum_Ico [division_ring α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i = (x ^ n - x ^ m) / (x - 1) :=
by simp only [sum_Ico_eq_sub _ hmn, (geom_sum_def _ _).symm, geom_sum_eq hx, div_sub_div_same,
  sub_sub_sub_cancel_right]

theorem geom_sum_Ico' [division_ring α] {x : α} (hx : x ≠ 1) {m n : ℕ} (hmn : m ≤ n) :
  ∑ i in finset.Ico m n, x ^ i = (x ^ m - x ^ n) / (1 - x) :=
by { simp only [geom_sum_Ico hx hmn], convert neg_div_neg_eq (x^m - x^n) (1-x); abel }

lemma geom_sum_inv [division_ring α] {x : α} (hx1 : x ≠ 1) (hx0 : x ≠ 0) (n : ℕ) :
  (geom_sum x⁻¹ n) = (x - 1)⁻¹ * (x - x⁻¹ ^ n * x) :=
have h₁ : x⁻¹ ≠ 1, by rwa [inv_eq_one_div, ne.def, div_eq_iff_mul_eq hx0, one_mul],
have h₂ : x⁻¹ - 1 ≠ 0, from mt sub_eq_zero.1 h₁,
have h₃ : x - 1 ≠ 0, from mt sub_eq_zero.1 hx1,
have h₄ : x * (x ^ n)⁻¹ = (x ^ n)⁻¹ * x :=
  nat.rec_on n (by simp)
  (λ n h, by rw [pow_succ, mul_inv_rev₀, ←mul_assoc, h, mul_assoc, mul_inv_cancel hx0, mul_assoc,
    inv_mul_cancel hx0]),
begin
  rw [geom_sum_eq h₁, div_eq_iff_mul_eq h₂, ← mul_right_inj' h₃,
    ← mul_assoc, ← mul_assoc, mul_inv_cancel h₃],
  simp [mul_add, add_mul, mul_inv_cancel hx0, mul_assoc, h₄, sub_eq_add_neg, add_comm,
    add_left_comm],
end

variables {β : Type*}

theorem ring_hom.map_geom_sum [semiring α] [semiring β] (x : α) (n : ℕ) (f : α →+* β) :
  f (geom_sum x n) = geom_sum (f x) n :=
by simp [geom_sum_def, f.map_sum]

theorem ring_hom.map_geom_sum₂ [semiring α] [semiring β] (x y : α) (n : ℕ) (f : α →+* β) :
  f (geom_sum₂ x y n) = geom_sum₂ (f x) (f y) n :=
by simp [geom_sum₂_def, f.map_sum]

/-! ### Geometric sum with `ℕ`-division -/

lemma nat.pred_mul_geom_sum_le (a b n : ℕ) :
  (b - 1) * ∑ i in range n.succ, a/b^i ≤ a * b - a/b^n :=
calc
  (b - 1) * (∑ i in range n.succ, a/b^i)
      = ∑ i in range n, a/b^(i + 1) * b + a * b
        - (∑ i in range n, a/b^i + a/b^n)
      : by rw [tsub_mul, mul_comm, sum_mul, one_mul, sum_range_succ',
          sum_range_succ, pow_zero, nat.div_one]
  ... ≤ ∑ i in range n, a/b^i + a * b - (∑ i in range n, a/b^i + a/b^n)
      : begin
        refine tsub_le_tsub_right (add_le_add_right (sum_le_sum $ λ i _, _) _) _,
        rw [pow_succ', ←nat.div_div_eq_div_mul],
        exact nat.div_mul_le_self _ _,
      end
  ... = a * b - a/b^n : add_tsub_add_eq_tsub_left _ _ _

lemma nat.geom_sum_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in range n, a/b^i ≤ a * b/(b - 1) :=
begin
  refine (nat.le_div_iff_mul_le _ _ $ tsub_pos_of_lt hb).2 _,
  cases n,
  { rw [sum_range_zero, zero_mul],
    exact nat.zero_le _ },
  rw mul_comm,
  exact (nat.pred_mul_geom_sum_le a b n).trans tsub_le_self,
end

lemma nat.geom_sum_Ico_le {b : ℕ} (hb : 2 ≤ b) (a n : ℕ) :
  ∑ i in Ico 1 n, a/b^i ≤ a/(b - 1) :=
begin
  cases n,
  { rw [Ico_eq_empty_of_le zero_le_one, sum_empty],
    exact nat.zero_le _ },
  rw ←add_le_add_iff_left a,
  calc
    a + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i
        = a/b^0 + ∑ (i : ℕ) in Ico 1 n.succ, a/b^i : by rw [pow_zero, nat.div_one]
    ... = ∑ i in range n.succ, a/b^i : begin
          rw [range_eq_Ico, ←nat.Ico_insert_succ_left (nat.succ_pos _), sum_insert],
          exact λ h, zero_lt_one.not_le (mem_Ico.1 h).1,
        end
    ... ≤ a * b/(b - 1) : nat.geom_sum_le hb a _
    ... = (a * 1 + a * (b - 1))/(b - 1)
        : by rw [←mul_add, add_tsub_cancel_of_le (one_le_two.trans hb)]
    ... = a + a/(b - 1)
        : by rw [mul_one, nat.add_mul_div_right _ _ (tsub_pos_of_lt hb), add_comm]
end
