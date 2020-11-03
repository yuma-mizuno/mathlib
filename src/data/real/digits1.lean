/-
Copyright (c) 2019 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Calle Sönne
-/

import algebra.archimedean tactic.linarith tactic.ring
import analysis.normed_space.basic order.filter.basic
import topology.algebra.ordered

/-
This file provides decimal (and more generally base b>=2) expansions of "floor rings",
that is, ordered rings equipped with a floor function to the integers, such as
the rational or real numbers.
If r is an element of such a ring, then expansion.digit b r n is the (n+1)'st digit
after the decimal point in the base b expansion of r, so 0 <= expansion.digit b r n < b.
In other words, if aₙ = expansion.digit b r n then for a real number r, we have
r = (floor r) + 0.a₀a₁a₂... in base b. We have 0 ≤ aₙ < b (digit_lt_base).
-/

namespace expansion

open filter

variables {α : Type*} [linear_ordered_ring α] [floor_ring α]

lemma mul_floor_le (a : α) {z : ℤ} (hz : 0 ≤ z) : floor(a)*z ≤ floor(a*z) :=
begin
rw [le_floor, int.cast_mul], rw [le_iff_eq_or_lt] at hz, cases hz with h₁ h₂,
{ rw [←h₁, int.cast_zero, mul_zero, mul_zero]},
{ rw [mul_le_mul_right], exact floor_le a, rw [←int.cast_zero], apply int.cast_lt.2, exact h₂},
end

definition digit (b : ℕ) (r : α) (n : ℕ) := floor(r * b ^ (n+1)) - floor(r * b ^ n)*b

lemma digit_lt_base {b : ℕ} (hb : 0 < b) (r : α) (n : ℕ) : digit b r n < b :=
begin
  unfold digit, rw [sub_lt_iff_lt_add, floor_lt, pow_add, pow_one, ←mul_assoc],
  rw [int.cast_add, int.cast_mul, int.cast_coe_nat],
  suffices : r * ↑b ^ n * ↑b < (1 + ↑⌊r * ↑b ^ n⌋) * ↑b, { by rwa [add_mul, one_mul] at this},
  rw [mul_lt_mul_right (nat.cast_pos.2 hb), add_comm], exact lt_floor_add_one (r * ↑b ^ n),
end

lemma zero_le_digit {b : ℕ} (r : α) (n : ℕ) : 0 ≤ digit b r n :=
begin
  rw [digit, le_sub, sub_zero, pow_add, pow_one, ←mul_assoc],
  exact mul_floor_le (r * ↑b ^ n) (int.coe_nat_nonneg b),
end

theorem approx {b : ℕ} (hb : 0 < b) (r : α) (n : ℕ) :
    ⌊(fract r * b ^ n)⌋ = finset.sum (finset.range n) (λ i, digit b r i * b ^ (n-1-i)) :=
begin
  induction n with n hn,
    { rw [pow_zero,mul_one,finset.range_zero,finset.sum_empty, floor_eq_iff],
    exact ⟨fract_nonneg _, by convert (fract_lt_one _);simp⟩},
    { rw [finset.sum_range_succ, ←nat.add_one, nat.add_sub_cancel, nat.sub_self, pow_zero, mul_one],
      rw [←domain.mul_right_inj (int.coe_nat_ne_zero_iff_pos.2 hb), finset.sum_mul] at hn,
      simp only [mul_assoc, (pow_succ' _ _).symm] at hn,
      rw [←@sub_right_inj _ _ (⌊fract r * ↑b ^ n⌋ * ↑b)], conv {to_rhs, rw hn},
      rw [add_sub_assoc, ←finset.sum_sub_distrib, fract, sub_mul, sub_mul],
      repeat {rw [←nat.cast_pow b, ←int.cast_coe_nat, ←int.cast_mul, floor_sub_int]},
      rw [sub_mul, mul_assoc, ←int.coe_nat_mul, ←nat.pow_succ, ←nat.add_one],
      rw [sub_sub_sub_cancel_right], rw [int.cast_coe_nat, int.cast_coe_nat, nat.cast_pow],
      rw [nat.cast_pow, ←digit], conv {to_lhs, rw ←add_zero (digit b r n)},
      rw [add_left_cancel_iff], cases n, { rw [finset.range_zero, finset.sum_empty]},
      apply eq.symm, apply finset.sum_eq_zero, intros x Hx, simp, rw [←nat.add_one],
      rw [finset.mem_range] at Hx,
      rw [add_comm n 1, nat.add_sub_assoc (nat.le_of_lt_succ Hx), add_neg_self]},
end

section limit

variables (β : Type*) [discrete_linear_ordered_field β] [floor_ring β] [topological_space β]
  [orderable_topology β]

theorem expansion_tendsto {b : ℕ} (hb : 1 < b) (r : β) (N : ℕ) :
  tendsto (λ n : ℕ, finset.sum (finset.range n)
    (λ i, (((digit b r i * b ^ (n - 1 - i)) : ℤ) : β) * (b ^ n)⁻¹))
    at_top (nhds (fract r)) :=
begin
--  rw tendsto_orderable,
  apply tendsto_orderable.2,
    swap, apply_instance, swap, apply_instance,
  split,
  { intros a ha,
    conv in (finset.sum _ _) begin
      rw ←finset.sum_mul,
      rw finset.sum
    end,
    sorry
  },
  {
    sorry
  }
end

#exit
intros n Hn,
rw [←approx (lt_trans (zero_lt_one) (hb)), fract, normed_ring.dist_eq],
end

end expansion
