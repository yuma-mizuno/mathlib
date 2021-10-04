/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
import analysis.calculus.mean_value
import analysis.normed_space.exponential
import analysis.special_functions.pow_calculus

/-!
# Collection of convex functions

In this file we prove that the following functions are convex:

* `convex_on_exp` : the exponential function is convex on $(-∞, +∞)$;
* `convex_on_pow_of_even` : given an even natural number $n$, the function $f(x)=x^n$
  is convex on $(-∞, +∞)$;
* `convex_on_pow` : for a natural $n$, the function $f(x)=x^n$ is convex on $[0, +∞)$;
* `convex_on_fpow` : for an integer $m$, the function $f(x)=x^m$ is convex on $(0, +∞)$.
* `convex_on_rpow : ∀ p : ℝ, 1 ≤ p → convex_on ℝ (Ici 0) (λ x, x ^ p)`
* `concave_on_log_Ioi` and `concave_on_log_Iio`: log is concave on `Ioi 0` and `Iio 0` respectively.
-/

open real set
open_locale big_operators nat

lemma const_add_tsum {ι β} [add_comm_monoid β] [topological_space β] [t2_space β]
  [has_continuous_add β]
  {f : ι → β} (hf : summable f) {c : β} (i : ι) [decidable_pred (λ n, n = i)] :
  c + ∑' n, f n = ∑' n, ite (n = i) (c + f i) (f n) :=
begin
  have h_const_eq_tsum : c = ∑' n, ite (n=i) c 0, from (tsum_ite_eq i c).symm,
  nth_rewrite 0 h_const_eq_tsum,
  rw ← tsum_add _ hf,
  { congr' with n,
    by_cases hni : n = i; simp [hni], },
  { refine summable_of_ne_finset_zero _,
    { exact {i}, },
    { intros n hni,
      rw finset.mem_singleton at hni,
      rw if_neg hni, }, },
end

lemma convex_exp_aux {x : ℝ} (hx : 0 < x) {b : ℝ} (hb_nonneg : 0 ≤ b) (hb_le : b ≤ 1) :
  exp (b * x) ≤ 1 - b + b * exp x :=
begin
  have hb_n_le : ∀ n : ℕ, 1 ≤ n → b ^ n ≤ b,
    by { intros h hn, nth_rewrite 1 ← pow_one b, exact pow_le_pow_of_le_one hb_nonneg hb_le hn, },
  rw [real.exp_eq_exp_ℝ_ℝ, exp_eq_tsum],
  dsimp only,
  rw [← tsum_mul_left, const_add_tsum _ 0],
  swap, { apply_instance, },
  swap, { apply_instance, },
  swap, { refine summable.mul_left b _, exact exp_series_summable' x, },
  refine tsum_le_tsum (λ n, _) _ _,
  { by_cases hn0 : n = 0,
    { simp [hn0], },
    simp only [hn0, one_div, if_false, smul_eq_mul],
    rw [mul_pow, ← mul_assoc, mul_comm _ (b ^ n), mul_assoc],
    refine mul_le_mul (hb_n_le n _) le_rfl _ hb_nonneg,
    { rw nat.succ_le_iff,
      exact lt_of_le_of_ne zero_le' (ne.symm hn0), },
    { refine mul_nonneg (inv_nonneg.mpr _) (pow_nonneg hx.le n),
      norm_cast, exact zero_le', } },
  { exact exp_series_summable' (b * x), },
  { refine (finset.summable_compl_iff {(0 : ℕ)}).mp _,
    have : (λ (m : {x : ℕ // x ∉ {(0 : ℕ)}}),
        ite ((m : ℕ) = 0) (1 - b + b * (1 / ((0 : ℕ)! : ℝ)) • x ^ 0)
          (b * (1 / ((m : ℕ)! : ℝ)) • x ^ (m : ℕ)))
      = (λ (m : {x : ℕ // x ∉ ({(0 : ℕ)} : finset ℕ)}), (b * (1 / ((m : ℕ)! : ℝ) * x ^ (m : ℕ)))),
    { ext1 m,
      have hm : (m : ℕ) ≠ (0 : ℕ), from mt finset.mem_singleton.mpr m.prop,
      simp only [hm, one_div, mul_eq_mul_left_iff, if_false, smul_eq_mul],
      exact or.inl (or.inl rfl), },
    rw this,
    rw @finset.summable_compl_iff _ _ _ _ _
      (λ m, b * (1 / ((m : ℕ)! : ℝ) * x ^ (m : ℕ))) {(0 : ℕ)},
    refine summable.mul_left b _,
    convert exp_series_summable' x,
    ext1 n,
    rw smul_eq_mul, },
end

lemma convex_on_exp_aux_2 {x y a b : ℝ} (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b)
  (hab_add : a + b = 1) (h_lt : x < y) :
  exp (a • x + b • y) ≤ a • exp x + b • exp y :=
begin
  have ha_eq : a = 1 - b, from eq_sub_iff_add_eq.mpr hab_add,
  simp_rw [ha_eq, smul_eq_mul],
  rw [sub_mul, one_mul],
  have hb_le_one : b ≤ 1, by linarith,
  calc exp (x - b * x + b * y) = exp x * exp (b * (y - x)) :
    by { rw ← real.exp_add, congr' 1, ring, }
  ... ≤ exp x * (1 - b + b * exp (y - x)) : mul_le_mul le_rfl
    (convex_exp_aux (sub_pos.mpr h_lt) hb_nonneg hb_le_one) (exp_pos _).le (exp_pos _).le
  ... = (1 - b) * exp x + b * exp y : begin
    rw [mul_add, mul_comm],
    congr' 1,
    rw [mul_comm, mul_assoc, ← real.exp_add, sub_add_cancel],
  end,
end

/-- `exp` is convex on the whole real line -/
lemma convex_on_exp : convex_on ℝ univ exp :=
begin
  refine ⟨convex_univ, λ x y _ _ a b ha_nonneg hb_nonneg hab_add, _⟩,
  rcases lt_trichotomy x y with h_lt|h_eq|h_lt,
  { exact convex_on_exp_aux_2 ha_nonneg hb_nonneg hab_add h_lt, },
  { simp_rw [h_eq, ← add_smul],
    rw [hab_add, one_smul, one_smul], },
  { rw add_comm at hab_add ⊢,
    rw add_comm (a • exp x),
    exact convex_on_exp_aux_2 hb_nonneg ha_nonneg hab_add h_lt, },
end
--convex_on_univ_of_deriv2_nonneg differentiable_exp (by simp)
--  (assume x, (iter_deriv_exp 2).symm ▸ le_of_lt (exp_pos x))

/-- `x^n`, `n : ℕ` is convex on the whole real line whenever `n` is even -/
lemma convex_on_pow_of_even {n : ℕ} (hn : even n) : convex_on ℝ set.univ (λ x : ℝ, x^n) :=
begin
  apply convex_on_univ_of_deriv2_nonneg differentiable_pow,
  { simp only [deriv_pow', differentiable.mul, differentiable_const, differentiable_pow] },
  { intro x,
    rcases nat.even.sub_even hn (nat.even_bit0 1) with ⟨k, hk⟩,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub, hk, pow_mul'],
    exact mul_nonneg (nat.cast_nonneg _) (pow_two_nonneg _) }
end

/-- `x^n`, `n : ℕ` is convex on `[0, +∞)` for all `n` -/
lemma convex_on_pow (n : ℕ) : convex_on ℝ (Ici 0) (λ x : ℝ, x^n) :=
begin
  apply convex_on_of_deriv2_nonneg (convex_Ici _) (continuous_pow n).continuous_on
    differentiable_on_pow,
  { simp only [deriv_pow'], exact (@differentiable_on_pow ℝ _ _ _).const_mul (n : ℝ) },
  { intros x hx,
    rw [iter_deriv_pow, finset.prod_range_cast_nat_sub],
    exact mul_nonneg (nat.cast_nonneg _) (pow_nonneg (interior_subset hx) _) }
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

/-- `x^m`, `m : ℤ` is convex on `(0, +∞)` for all `m` -/
lemma convex_on_fpow (m : ℤ) : convex_on ℝ (Ioi 0) (λ x : ℝ, x^m) :=
begin
  have : ∀ n : ℤ, differentiable_on ℝ (λ x, x ^ n) (Ioi (0 : ℝ)),
    from λ n, differentiable_on_fpow _ _ (or.inl $ lt_irrefl _),
  apply convex_on_of_deriv2_nonneg (convex_Ioi 0);
    try { simp only [interior_Ioi, deriv_fpow'] },
  { exact (this _).continuous_on },
  { exact this _ },
  { exact (this _).const_mul _ },
  { intros x hx,
    simp only [iter_deriv_fpow, ← int.cast_coe_nat, ← int.cast_sub, ← int.cast_prod],
    refine mul_nonneg (int.cast_nonneg.2 _) (fpow_nonneg (le_of_lt hx) _),
    exact int_prod_range_nonneg _ _ (nat.even_bit0 1) }
end

lemma convex_on_rpow {p : ℝ} (hp : 1 ≤ p) : convex_on ℝ (Ici 0) (λ x : ℝ, x^p) :=
begin
  have A : deriv (λ (x : ℝ), x ^ p) = λ x, p * x^(p-1), by { ext x, simp [hp] },
  apply convex_on_of_deriv2_nonneg (convex_Ici 0),
  { exact continuous_on_id.rpow_const (λ x _, or.inr (zero_le_one.trans hp)) },
  { exact (differentiable_rpow_const hp).differentiable_on },
  { rw A,
    assume x hx,
    replace hx : x ≠ 0, by { simp at hx, exact ne_of_gt hx },
    simp [differentiable_at.differentiable_within_at, hx] },
  { assume x hx,
    replace hx : 0 < x, by simpa using hx,
    suffices : 0 ≤ p * ((p - 1) * x ^ (p - 1 - 1)), by simpa [ne_of_gt hx, A],
    apply mul_nonneg (le_trans zero_le_one hp),
    exact mul_nonneg (sub_nonneg_of_le hp) (rpow_nonneg_of_nonneg (le_of_lt hx) _) }
end

lemma concave_on_log_Ioi : concave_on ℝ (Ioi 0) log :=
begin
  have h₁ : Ioi 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Ioi 0) is_open_Ioi _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    rw [function.iterate_succ, function.iterate_one],
    change (deriv (deriv log)) x ≤ 0,
    rw [deriv_log', deriv_inv],
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x)) }
end

lemma concave_on_log_Iio : concave_on ℝ (Iio 0) log :=
begin
  have h₁ : Iio 0 ⊆ ({0} : set ℝ)ᶜ,
  { intros x hx hx',
    rw [mem_singleton_iff] at hx',
    rw [hx'] at hx,
    exact lt_irrefl 0 hx },
  refine concave_on_open_of_deriv2_nonpos (convex_Iio 0) is_open_Iio _ _ _,
  { exact differentiable_on_log.mono h₁ },
  { refine ((times_cont_diff_on_log.deriv_of_open _ le_top).differentiable_on le_top).mono h₁,
    exact is_open_compl_singleton },
  { intros x hx,
    rw [function.iterate_succ, function.iterate_one],
    change (deriv (deriv log)) x ≤ 0,
    rw [deriv_log', deriv_inv],
    exact neg_nonpos.mpr (inv_nonneg.mpr (sq_nonneg x)) }
end
