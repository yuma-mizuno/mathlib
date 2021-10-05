/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.mean_inequalities_exp
import analysis.special_functions.pow

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on ℝ (Ici 0) (λ x, x ^ p)`
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
-/

open real set
open_locale big_operators nat

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  refine ⟨convex_Ici 0, λ x y hx hy a b ha hb hab_add, _⟩,
  rw mem_Ici at hx hy,
  dsimp only,
  by_cases ha0 : a = 0,
  { have hb : b = 1, by rwa [ha0, zero_add] at hab_add,
    simp [ha0, hb], },
  by_cases hb0 : b = 0,
  { have ha : a = 1, by rwa [hb0, add_zero] at hab_add,
    simp [hb0, ha], },
  have ha_pos : 0 < a, from lt_of_le_of_ne ha (ne.symm ha0),
  have hb_pos : 0 < b, from lt_of_le_of_ne hb (ne.symm hb0),
  by_cases hp_eq_one : p = 1,
  { simp [hp_eq_one], },
  have hp_one_lt : 1 < p, from lt_of_le_of_ne hp (ne.symm hp_eq_one),
  let q := conjugate_exponent p,
  have hpq : p.is_conjugate_exponent q := is_conjugate_exponent_conjugate_exponent hp_one_lt,
  have ha_eq : a = a ^ (1/p) * a ^ (1/q), by rw [← rpow_add ha_pos, hpq.inv_add_inv_conj, rpow_one],
  have hb_eq : b = b ^ (1/p) * b ^ (1/q), by rw [← rpow_add hb_pos, hpq.inv_add_inv_conj, rpow_one],
  nth_rewrite 0 ha_eq,
  nth_rewrite 0 hb_eq,
  calc (a ^ (1/p) * a ^ (1/q) * x + b ^ (1/p) * b ^ (1/q) * y) ^ p
      = (a ^ (1/p) * x * a ^ (1/q) + b ^ (1/p) * y * b ^ (1/q)) ^ p : by { congr' 2, ring, ring, }
  ... ≤ (((a^(1/p) * x)^p + (b^(1/p) * y)^p)^(1/p) * ((a^(1/q))^q + (b^(1/q))^q)^(1/q)) ^ p : by {
    refine rpow_le_rpow _ _ hpq.nonneg,
    { exact add_nonneg
        (mul_nonneg (mul_nonneg (rpow_nonneg_of_nonneg ha _) hx) (rpow_nonneg_of_nonneg ha _))
        (mul_nonneg (mul_nonneg (rpow_nonneg_of_nonneg hb _) hy) (rpow_nonneg_of_nonneg hb _)), },
    { exact inner_le_Lp_mul_Lq_of_nonneg2 hpq (mul_nonneg (rpow_nonneg_of_nonneg ha _) hx)
        (mul_nonneg (rpow_nonneg_of_nonneg hb _) hy) (rpow_nonneg_of_nonneg ha _)
        (rpow_nonneg_of_nonneg hb _), }, }
  ... = a * x ^ p + b * y ^ p : by {
    rw [← rpow_mul hb, ← rpow_mul ha, one_div, one_div, inv_mul_cancel hpq.symm.ne_zero, rpow_one,
      rpow_one, hab_add, one_rpow, mul_one, mul_rpow (rpow_nonneg_of_nonneg ha _) hx,
      mul_rpow (rpow_nonneg_of_nonneg hb _) hy, ← rpow_mul ha, ← rpow_mul hb,
      inv_mul_cancel hpq.ne_zero, rpow_one, rpow_one, ← rpow_mul, inv_mul_cancel hpq.ne_zero,
      rpow_one],
    exact add_nonneg (mul_nonneg ha (rpow_nonneg_of_nonneg hx _))
      (mul_nonneg hb (rpow_nonneg_of_nonneg hy _)), },
end

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma convex_on_pow_of_even {n : ℕ} (hn : even n) : convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  refine ⟨convex_univ, λ x y hx hy a b ha hb hab_add, _⟩,
  dsimp only,
  by_cases hn0 : n = 0,
  { simp [hn0, hab_add.symm.le], },
  suffices : (a • abs x + b • abs y) ^ (n : ℝ) ≤ a • (abs x) ^ (n : ℝ) + b • (abs y) ^ (n : ℝ),
  { simp_rw rpow_nat_cast at this,
    have h_abs : ∀ x : ℝ, abs x ^ n = x ^ n, from λ x, pow_even_abs _ hn,
    rw [h_abs x, h_abs y] at this,
    rw ← h_abs (a • x + b • y),
    calc abs (a • x + b • y) ^ n ≤ (abs (a • x) + abs (b • y)) ^ n :
      pow_le_pow_of_le_left (abs_nonneg _) (abs_add _ _) n
    ... = (a • abs x + b • abs y) ^ n :
      by simp_rw [smul_eq_mul, abs_mul, abs_eq_self.mpr ha, abs_eq_self.mpr hb]
    ... ≤ a • x ^ n + b • y ^ n : this, },
  refine (convex_on_rpow _).2 (mem_Ici.mpr (abs_nonneg x)) (mem_Ici.mpr (abs_nonneg y))
    ha hb hab_add,
  norm_cast,
  rw nat.succ_le_iff,
  exact lt_of_le_of_ne zero_le' (ne.symm hn0),
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  refine ⟨convex_Ici 0, λ x y hx hy a b ha hb hab_add, _⟩,
  rw mem_Ici at hx hy,
  dsimp only,
  by_cases hn0 : n = 0,
  { simp [hn0,hab_add.symm.le], },
  suffices : (a • x + b • y) ^ (n : ℝ) ≤ a • x ^ (n : ℝ) + b • y ^ (n : ℝ),
  { simp_rw rpow_nat_cast at this, exact this, },
  refine (convex_on_rpow _).2 hx hy ha hb hab_add,
  norm_cast,
  rw nat.succ_le_iff,
  exact lt_of_le_of_ne zero_le' (ne.symm hn0),
end

lemma finset.prod_nonneg_of_card_nonpos_even
  {α β : Type*} [linear_ordered_comm_ring β]
  {f : α → β} [decidable_pred (λ x, f x ≤ 0)]
  {s : finset α} (h0 : even (s.filter (λ x, f x ≤ 0)).card) :
  0 ≤ ∏ x in s, f x :=
calc 0 ≤ (∏ x in s, ((if f x ≤ 0 then (-1:β) else 1) * f x)) :
  finset.prod_nonneg (λ x _, by
    { split_ifs with hx hx, by simp [hx], simp at hx ⊢, exact le_of_lt hx })
... = _ : by rw [finset.prod_mul_distrib, finset.prod_ite, finset.prod_const_one,
  mul_one, finset.prod_const, neg_one_pow_eq_pow_mod_two, nat.even_iff.1 h0, pow_zero, one_mul]

lemma int_prod_range_nonneg (m : ℤ) (n : ℕ) (hn : even n) :
  0 ≤ ∏ k in finset.range n, (m - k) :=
begin
  rcases hn with ⟨n, rfl⟩,
  induction n with n ihn, { simp },
  rw [nat.succ_eq_add_one, mul_add, mul_one, bit0, ← add_assoc, finset.prod_range_succ,
    finset.prod_range_succ, mul_assoc],
  refine mul_nonneg ihn _, generalize : (1 + 1) * n = k,
  cases le_or_lt m k with hmk hmk,
  { have : m ≤ k + 1, from hmk.trans (lt_add_one ↑k).le,
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hmk) (sub_nonpos.2 this) },
  { exact mul_nonneg (sub_nonneg.2 hmk.le) (sub_nonneg.2 hmk) }
end

lemma convex_on_fpow_of_nonneg (m : ℤ) (hm : 0 ≤ m) : convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  refine ⟨convex_Ioi 0, λ x y hx hy a b ha hb hab_add, _⟩,
  rw mem_Ioi at hx hy,
  dsimp only,
  by_cases hm0 : m = 0,
  { simp [hm0, hab_add.symm.le], },
  suffices : (a • x + b • y) ^ (m : ℝ) ≤ a • x ^ (m : ℝ) + b • y ^ (m : ℝ),
  { simp_rw rpow_int_cast at this, exact this, },
  refine (convex_on_rpow _).2 hx.le hy.le ha hb hab_add,
  norm_cast,
  rw [← zero_add (1 : ℤ), int.add_one_le_iff],
  exact lt_of_le_of_ne hm (ne.symm hm0),
end

lemma two_le_add_inv {x : ℝ} (hx : 0 < x) : 2 ≤ x + x⁻¹ :=
le_of_mul_le_mul_left
  (sub_nonneg.1 $
    calc 0 ≤ (x - 1) ^ 2 : pow_two_nonneg _
       ... = _ : by field_simp [ne_of_gt hx]; ring)
  hx


/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_fpow (m : ℤ) : convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  by_cases hm_nonneg : 0 ≤ m,
  { exact convex_on_fpow_of_nonneg m hm_nonneg, },
  have h_neg_m_nonneg : 0 ≤ - m, from neg_nonneg.mpr (le_of_not_le hm_nonneg),
  refine ⟨convex_Ioi 0, λ x y hx hy a b ha hb hab_add, _⟩,
  rw mem_Ioi at hx hy,
  dsimp only,
  by_cases ha0 : a = 0,
  { have hb : b = 1, by rwa [ha0, zero_add] at hab_add,
    simp [ha0, hb], },
  have ha_pos : 0 < a, from lt_of_le_of_ne ha (ne.symm ha0),
  suffices : 1 ≤ a • (a + b • (y/x)) ^ (-m) + b • (a • (x/y) + b) ^ (-m),
  { have h_eq_div : ∀ r : ℝ, r ^ m = (1 / r) ^ (-m), by {intro r, simp, },
    simp_rw smul_eq_mul at this ⊢,
    rw [h_eq_div (a * x + b * y), div_fpow, one_fpow, div_le_iff, add_mul, h_eq_div x, h_eq_div y,
      mul_assoc, ← mul_fpow, mul_assoc, ← mul_fpow, mul_add, mul_add],
    swap, { refine fpow_pos_of_pos _ _,
      exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx) (mul_nonneg hb hy.le), },
    refine this.trans (le_of_eq _),
    congr' 4,
    { rw [one_div, mul_comm, mul_assoc, mul_inv_cancel hx.ne.symm, mul_one], },
    { rw [one_div, div_eq_mul_inv, ← mul_assoc, mul_comm], },
    { rw [one_div, div_eq_mul_inv, ← mul_assoc, mul_comm], },
    { rw [one_div, mul_comm, mul_assoc, mul_inv_cancel hy.ne.symm, mul_one], }, },
  have h_sq_le : (a + b) ^ 2 ≤ a • (a + b • (y / x)) + b • (a • (x / y) + b),
  { have h_two_le : 2 ≤ y/x + x/y, by { convert two_le_add_inv (div_pos hy hx), rw inv_div, },
    simp_rw smul_eq_mul,
    calc (a + b) ^ 2 = a * a + 2 * a * b + b * b : by ring
    ... ≤ a * a + (y/x + x/y) * a * b + b * b : by {
      refine add_le_add (add_le_add le_rfl _) le_rfl,
      rw [mul_assoc, mul_assoc],
      refine mul_le_mul h_two_le le_rfl (mul_nonneg ha hb) _,
      exact (add_nonneg (div_nonneg hy.le hx.le) (div_nonneg hx.le hy.le)), }
    ... = a * (a + b * (y / x)) + b * (a * (x / y) + b) : by ring, },
  calc 1 = ((a + b) ^ 2) ^ (-m) : by { simp [hab_add], }
  ... ≤ (a • (a + b • (y/x)) + b • (a • (x/y) + b)) ^ (-m) : by {
    suffices : ((a + b) ^ 2) ^ (-m : ℝ) ≤ (a • (a + b • (y/x)) + b • (a • (x/y) + b)) ^ (-m : ℝ),
    { have hm_cast : ((-m : ℤ) : ℝ) = - m, by norm_cast,
      simp_rw [← hm_cast, rpow_int_cast] at this, exact this, },
    refine rpow_le_rpow (sq_nonneg _) h_sq_le _,
    norm_cast,
    exact h_neg_m_nonneg, }
  ... ≤ a • (a + b • (y/x)) ^ (-m) + b • (a • (x/y) + b) ^ (-m) :
    (convex_on_fpow_of_nonneg (-m) h_neg_m_nonneg).2 (mem_Ioi.mpr _) (mem_Ioi.mpr _) ha hb hab_add,
  { exact add_pos_of_pos_of_nonneg ha_pos (mul_nonneg hb (div_nonneg hy.le hx.le)), },
  { exact add_pos_of_pos_of_nonneg (mul_pos ha_pos (div_pos hx hy)) hb, },
end
