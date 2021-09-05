/-
Copyright (c) 2021 Artem Vasilev, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artem Vasilev, Yaël Dillies
-/
import analysis.mean_inequalities
import data.multiset.basic
import data.real.sqrt
import logic.relation

/-!
# The Oxford Invariants Puzzle Challenges - Summer 2021, Week 6, Problem 2

## Original statement

On the table there are written numbers `1, 2, ... n`. In each step we erase any
two of the numbers `x, y` and replace it with `2x + 2y`. THe procedure is repeated
until there is only one number remaining. Show that this number is not smaller than `4/9 n^3`.

## Proof outline

The proof consists of two parts. First, we show that the sum of square roots
of all numbers on the table is non-decreasing. Second, we show that
the sum of square roots of `1, 2, ..., n` is at least `2/3 n^(3/2)`.
Combining these two statements, we show that the square root of the last remaining number
is at least `2/3 n^(3/2)`, or, equivalently, that number is at least `4/9 n^3`.

Proving the first statement is equivalent to showing
that for any two natural numbers `x`, `y`, `√x + √y ≤ √(2 * (x + y))`.
Squaring this inequality, we get `x + 2√x√y + y ≤ 2(x + y)`,
which we get from the standard AM-GM inequality.

There are two ways to bound the sum of square roots `√1 + √2 + ... + √n ≥ 2/3 n^3/2`.
The first way is to prove it by induction on `n`.
The second way is to bound the sum from below by the integral $\int_0^n \sqrt{x} dx = 2/3 n^{3/2}$.

We are going to prove $\sqrt{4/9 n^3} \le \sum_{k=0}^{n} \sqrt{k}$ by induction.

The case `n = 0` is trivial. We also solve the case `n = 1` separately,
because one step in the induction proof below does not work for `n = 1`.

For `n + 1`, we need to prove $\sqrt{4/9 (n+1)^3} \le \sum_{k=0}^{n+1} \sqrt{k}$.
Using the induction hypothesis, it's enough to prove that
$\sqrt{4/9 (n+1)^3} \le \sqrt{4/9 n^3} + \sqrt{n+1}$.

* $\sqrt{4/9 (n+1)^3} \le \sqrt{4/9 n^3} + \sqrt{n+1}$
* $4/9 (n+1)^3 \le 4/9 n^3 + 2 \sqrt{4/9 n^3} \sqrt{n+1} + n+1$
* $4/9 (n+1)^3 - 4/9 n^3 - n - 1 \le 2 \sqrt{4/9 n^3} \sqrt{n+1}$*
* The left side of this inequality is negative for `n = 1`, and positive for all greater values.
* $(4/9 (n+1)^3 - 4/9 n^3 - n - 1)^2 \le 4 (4/9 n^3)(n + 1)$
* Collecting all terms of this degree-3 polynomial on one side, we get:
* $0 \le -25/81 + 10/27n + 37/27 n^2 + 8/9 n^3$
* This is true for all `n ≥ 1`.

## Formalising the proof

We model the process in the problem statement as a binary relation on the multisets.
We define the relation `one_step s t` if, given the multiset `s` of numbers on the table,
we can get `t` to be the multiset of numbers in one step of taking two numbers `x` and `y`
from `s` and replacing them with `2(x + y)`.

This is done by defining `one_step` as an inductive data type
with one constructor `step (x ::ₘ y ::ₘ m) (2 * (x + y) ::ₘ m)`
(the notation `x ::ₘ m` means inserting `x` into multiset `m`).
For the binary relation relating all pairs of multisets `s` and `t`,
where `t` can be obtained from `s` in zero or more steps,
we use the reflexive-transitive closure of `one_step`.
In Lean, this is done by `relation.refl_trans_gen one_step`.

Then, we show that if the monovariant is monotone for one step,
then it's monotone for any pair in the refl-trans closure.
This is done for a general function `f : α → β` with a preorder on `β`,
though it can be further generalized.

The hardest part in this proof is showing all the inequalities regarding reals.
Some of the work here is done with `nnreal` or `ℝ≥0` (non-negative reals) type,
to save the trouble of proving that `0 ≤ x` whenever we work with `sqrt x`.
The `real` or `ℝ` type has a lot richer API and tactic support,
so in many cases, we switch to reals.

The general weighted AM-GM inequality we use is `geom_mean_le_arith_mean2_weighted`
in `analysis.mean_inequalities`. The inequality we need to prove the monovariant
is the lemma `sqrt_add_sqrt_le_sqrt_two_mul_add` in `namespace nnreal`.

The proof sum of square roots lower bound is  the lemma `le_sum_sqrt`.
The proof is done by induction on `n`. Steps used to prove the inequality are described above
and use `real` and `nnreal` API from mathlib. We start working inside `nnreal` type
and move to `real`. To simplify the polynomial, we use the `ring_exp` tactic.
-/

open_locale big_operators nnreal
open relation nnreal

/-! ### For mathlib -/

namespace real

lemma two_mul_sqrt_le_add {x y : ℝ} (h : 0 ≤ x + y) :
  2 * sqrt (x * y) ≤ x + y :=
begin
  obtain hx | hx := lt_or_le x 0; obtain hy | hy := lt_or_le y 0,
  { rw ←add_zero (0 : ℝ) at h,
    exact ((add_lt_add hx hy).not_le h).elim },
  { rwa [sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hx.le hy), mul_zero] },
  { rwa [sqrt_eq_zero_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hx hy.le), mul_zero] },
  rw [sqrt_mul hx, sqrt_eq_rpow],
  linarith [geom_mean_le_arith_mean2_weighted one_half_pos.le one_half_pos.le hx hy (add_halves' 1)]
end

lemma sqrt_add_sqrt_le_sqrt_two_mul_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y):
  sqrt x + sqrt y ≤ sqrt (2 * (x + y)) :=
begin
  refine le_sqrt_of_sq_le _,
  rw [add_sq, sq_sqrt hx, sq_sqrt hy, add_right_comm, two_mul (x + y),
    add_le_add_iff_left, mul_assoc, ←sqrt_mul hx],
  exact two_mul_sqrt_le_add (add_nonneg hx hy),
end

end real

namespace nnreal

@[simp, norm_cast] lemma coe_sqrt {x : ℝ≥0} : (sqrt x : ℝ) = real.sqrt x :=
begin
  obtain ⟨x, hx⟩ := x,
  simp_rw [real.sqrt, real.to_nnreal, subtype.coe_mk, max_eq_left hx],
end

lemma two_mul_sqrt_le_add (x y : ℝ≥0) : 2 * sqrt (x * y) ≤ x + y :=
begin
  rw ←nnreal.coe_le_coe,
  push_cast,
  exact real.two_mul_sqrt_le_add (add_nonneg x.2 y.2),
end

lemma sqrt_add_sqrt_le_sqrt_two_mul_add (x y : ℝ≥0):
  sqrt x + sqrt y ≤ sqrt (2 * (x + y)) :=
begin
  rw ←nnreal.coe_le_coe,
  push_cast,
  exact real.sqrt_add_sqrt_le_sqrt_two_mul_add x.2 y.2,
end

end nnreal

/-! ### Actual stuff -/

variables {α : Type*}

/- The binary relation containing all pairs of multisets that can be obtained
by taking two numbers `x` and `y` and replacing them by `2 * (x + y)` -/
inductive one_step [semiring α] : multiset α → multiset α → Prop
| step {x y : α} {s : multiset α} : one_step (x ::ₘ y ::ₘ s) (2 * (x + y) ::ₘ s)

def can_reach [semiring α] : multiset α → multiset α → Prop := refl_trans_gen one_step

theorem mono_total_of_mono_step {β} [preorder β] {r : α → α → Prop} (f : α → β)
  (h : ∀ {x y}, r x y → f x ≤ f y) :
  ∀ {x y}, refl_trans_gen r x y → f x ≤ f y :=
begin
  rintro x y h₂,
  induction h₂ with x y _ rel_right ih,
  { refl },
  { exact ih.trans (h rel_right) },
end

lemma sum_sqrt_mono {s t : multiset ℕ} (h : one_step s t) :
  (s.map (sqrt ∘ coe)).sum ≤ (t.map (sqrt ∘ coe)).sum :=
begin
  induction h with x y m,
  simp only [multiset.map_cons, nat.cast_bit0, multiset.sum_cons, function.comp_app,
    nat.cast_add, nat.cast_one, nat.cast_mul],
  rw [←add_assoc],
  refine add_le_add_right (nnreal.sqrt_add_sqrt_le_sqrt_two_mul_add x y) _
end

lemma sum_sqrt_mono_of_can_reach {s t : multiset ℕ} (h : can_reach s t) :
  (s.map (sqrt ∘ coe)).sum ≤ (t.map (sqrt ∘ coe)).sum :=
begin
  -- `apply` and `convert` infer the correct types, `refine` and `exact` don't
  convert mono_total_of_mono_step (λ m : multiset ℕ, (m.map (sqrt ∘ coe)).sum) @sum_sqrt_mono h
end

theorem le_sum_sqrt {n : ℕ} : sqrt ((4 : ℝ≥0) / 9 * n^3) ≤  ∑ i in finset.Ico 1 n.succ, sqrt i :=
begin
  induction n with n ih,
  { simp },
  { obtain rfl | hpos := nat.eq_zero_or_pos n,
    { simp [sqrt_le_iff], rw ←nnreal.coe_le_coe, norm_num },
    rw [finset.Ico.succ_top (nat.succ_le_succ (nat.zero_le n)),
      finset.sum_insert (finset.Ico.not_mem_top)],
    refine (le_add_of_le_add_left _ ih),
    rw [sqrt_le_iff, add_mul_self_eq, mul_sqrt_self, mul_sqrt_self, ←nnreal.coe_le_coe],
    push_cast,
    rw [←_root_.sub_le_iff_le_add, ←sub_le_iff_le_add'],
    refine le_of_pow_le_pow 2 (mul_nonneg
      (mul_nonneg zero_le_two (real.sqrt_nonneg _)) (real.sqrt_nonneg _)) (zero_lt_two) _,
    rw [mul_pow _ _ 2, mul_pow _ _ 2,
      pow_two (real.sqrt (↑n + 1)),
      real.mul_self_sqrt (add_nonneg (nat.cast_nonneg n) (zero_le_one)),
      pow_two (real.sqrt ((4 : ℝ) / 9 * ↑n^3)),
      real.mul_self_sqrt
        (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ) / 9) (pow_nonneg (nat.cast_nonneg n) 3)),
      mul_assoc, add_mul, mul_add, ←sub_nonneg],
    ring_exp,
    rw [←nat.succ_le_iff, ←@nat.cast_le ℝ, nat.cast_one] at hpos,
    linarith [one_le_pow_of_one_le hpos 2, one_le_pow_of_one_le hpos 3], }
end

theorem week6_p2 {n x} (h : can_reach (multiset.Ico 1 (n + 1)) {x}) :
  (4 : ℝ≥0) / 9 * n^3 ≤ (x : ℝ≥0) :=
begin
  rw ←order_iso.le_iff_le sqrt,
  transitivity ((multiset.Ico 1 (n + 1)).map (sqrt ∘ coe)).sum,
  { exact le_sum_sqrt, },
  { convert sum_sqrt_mono_of_can_reach h,
    rw [multiset.map_singleton, multiset.sum_singleton], }
end
