/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes
-/

import algebra.euclidean_domain
import algebra.gcd_monoid.basic

/-!
# GCD monoid instance for Euclidean domains

This file provides the `gcd_monoid` instance for `euclidean_domain`s.

## Tags

euclidean domain, gcd
-/

namespace euclidean_domain

section gcd_monoid

variables {R : Type*} [euclidean_domain R] [gcd_monoid R]

open gcd_monoid

lemma left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) :
  p / gcd_monoid.gcd p q ≠ 0 :=
begin
  obtain ⟨r, hr⟩ := gcd_monoid.gcd_dvd_left p q,
  obtain ⟨pq0, r0⟩ : gcd_monoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp),
  rw [hr, mul_comm, mul_div_cancel _ pq0] { occs := occurrences.pos [1] },
  exact r0,
end

lemma right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) :
  q / gcd_monoid.gcd p q ≠ 0 :=
begin
  obtain ⟨r, hr⟩ := gcd_monoid.gcd_dvd_right p q,
  obtain ⟨pq0, r0⟩ : gcd_monoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq),
  rw [hr, mul_comm, mul_div_cancel _ pq0] { occs := occurrences.pos [1] },
  exact r0,
end

end gcd_monoid

variables {α : Type*} [euclidean_domain α] [decidable_eq α]

@[priority 100]  -- see Note [lower instance priority]
instance gcd_monoid : gcd_monoid α :=
{ gcd := gcd,
  lcm := lcm,
  gcd_dvd_left := gcd_dvd_left,
  gcd_dvd_right := gcd_dvd_right,
  dvd_gcd := λ a b c, dvd_gcd,
  gcd_mul_lcm := λ a b, by rw gcd_mul_lcm,
  lcm_zero_left := lcm_zero_left,
  lcm_zero_right := lcm_zero_right }

lemma gcd_eq_gcd (a b : α) : gcd_monoid.gcd a b = euclidean_domain.gcd a b := rfl

end euclidean_domain
