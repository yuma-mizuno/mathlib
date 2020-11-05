/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import data.real.basic
import tactic

/-

This file provides decimal (and more generally base b>=2) expansions of "floor rings",
that is, ordered rings equipped with a floor function to the integers, such as
the rational or real numbers.

If r is an element of such a ring, then expansion.digit b r n is the (n+1)'st digit
after the decimal point in the base b expansion of r, so 0 <= expansion.digit b r n < b.
In other words, if aₙ = expansion.digit b r n then for a real number r, we have
r = (floor r) + 0.a₀a₁a₂... in base b. We have 0 ≤ aₙ < b (digit_lt_base).

-/

section generalities

open_locale big_operators

universe u

variables {R : Type u} [linear_ordered_ring R] [floor_ring R]

-- idea : base b expansion of a real number r

/-
Start by defining an auxiliary function `digit_aux`
This function is defined by recursion.
digit_aux b r 0 is (r-⌊r⌋)*b
so if r=N.a₁a₂a₃...then this number is a₁.a₂a₃...

and digit_aux b r n is a_{n+1}.a_{n+2}a_{n+3}... if r=N.a₁a₂a₃…
-/

-- fract r = r - ⌊r⌋

namespace floor_ring

/-- An auxiliary function which we'll use to define decimal expansions -/
def digit_aux (b : ℕ) (r : R) : ℕ → R
| 0 := fract r * b
| (n + 1) := fract (digit_aux n) * b

lemma digit_aux_nonneg (b : ℕ) (r : R) (n : ℕ) : 0 ≤ digit_aux b r n :=
begin
  cases n;
  exact mul_nonneg (fract_nonneg _) (by simp),
end

lemma digit_aux_lt_base {b : ℕ} (hb : 0 < b) (r : R) (n : ℕ) : digit_aux b r n < b :=
begin
  cases n,
  { show fract r * b < b,
    rw mul_lt_iff_lt_one_left,
    apply fract_lt_one,
    assumption_mod_cast },
  { show fract (digit_aux b r n) * b < b,
    rw mul_lt_iff_lt_one_left,
    apply fract_lt_one,
    assumption_mod_cast },
end

/-- digit b r n is the (n+1)st digit after the decimal point in the base b
  expansion of r -/
definition digit (b : ℕ) (r : R) (n : ℕ) : ℕ := int.to_nat (⌊digit_aux b r n⌋)

lemma digit_lt_base {b : ℕ} (hb : 0 < b) (r : R) (n : ℕ) : digit b r n < b :=
begin
  have h : (⌊digit_aux b r n⌋ : R) < b,
    exact lt_of_le_of_lt (floor_le _) (digit_aux_lt_base hb r n),
  have h2 : ⌊digit_aux b r n⌋ = digit b r n,
    exact (int.to_nat_of_nonneg (floor_nonneg.2 $ digit_aux_nonneg b r n)).symm,
  have h3 : ((digit b r n : ℤ) : R) < b,
     rwa ←h2,
  simpa using h3,
end

-- example (x y z : R) : x ≤ y → 0 ≤ z → x + z ≤ y :=
--   exact (mul_lt_mul_right hb).mpr hxy
-- end

-- something wrong here -- induction seems like a horrible pain
-- should be proving something else?
theorem approx {b : ℕ} (hb : 0 < b) (r : R) (n : ℕ) :
⌊((fract r) * b ^ n)⌋ = ∑ i in (finset.range n), b^(n - 1 - i) * digit b r i :=
begin
  induction n with m hm,
  { rw [pow_zero, mul_one, finset.sum_range_zero, floor_fract] },
  { rw floor_eq_iff at *,
    rw nat.succ_eq_add_one at *,
    cases hm with hm1 hm2,
    have hb' : (0 : R) < b,
      assumption_mod_cast,
    split,
    { rw ← mul_le_mul_right hb' at hm1,
      simp, -- why does index var change from i to x?
      rw finset.sum_range_succ,
      sorry
    },
    {
     sorry
    }

  }
end

end floor_ring

end generalities
