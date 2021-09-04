/-
Copyright (c) 2021 Artem Vasilev, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artem Vasilev, Yaël Dillies
-/
import analysis.mean_inequalities
import data.multiset.basic
import data.real.sqrt
import logic.relation

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

lemma le_sum_sqrt {n : ℕ} : sqrt ((4 : ℝ≥0) / 9 * n^3) ≤  ∑ i in finset.Ico 1 n.succ, sqrt i :=
begin
  induction n with n ih,
  { simp },
  { obtain rfl | hpos := nat.eq_zero_or_pos n,
    { simp [sqrt_le_iff], rw ←nnreal.coe_le_coe, norm_num },
    rw [finset.Ico.succ_top (nat.succ_le_succ_iff.2 (nat.zero_le n)),
      finset.sum_insert (finset.Ico.not_mem_top)],
    refine (le_add_of_le_add_left _ ih),
    rw [sqrt_le_iff, add_mul_self_eq, mul_sqrt_self, mul_sqrt_self, ←nnreal.coe_le_coe],
    push_cast,
    rw [←_root_.sub_le_iff_le_add, ←sub_le_iff_le_add'],
    refine le_of_pow_le_pow 2
      (mul_nonneg (mul_nonneg zero_le_two (real.sqrt_nonneg _)) (real.sqrt_nonneg _)) (zero_lt_two) _,
    rw [mul_pow _ _ 2, mul_pow _ _ 2,
      pow_two (real.sqrt (↑n + 1)),
      real.mul_self_sqrt (add_nonneg (nat.cast_nonneg n) (zero_le_one)),
      pow_two (real.sqrt ((4 : ℝ) / 9 * ↑n^3)),
      real.mul_self_sqrt (mul_nonneg (by norm_num : 0 ≤ (4 : ℝ) / 9) (pow_nonneg (nat.cast_nonneg n) 3)),
      mul_assoc, add_mul, mul_add, ←sub_nonneg],
    ring_exp,
    rw [←nat.succ_le_iff, ←@nat.cast_le ℝ, nat.cast_one] at hpos,
    linarith [one_le_pow_of_one_le hpos 2, one_le_pow_of_one_le hpos 3], }
end

/-! ### Actual stuff -/

variables {α : Type*}

inductive one_step [semiring α] : multiset α → multiset α → Prop
| step {x y : α} {m : multiset α} : one_step (x ::ₘ y ::ₘ m) ((2 * (x + y)) ::ₘ m)

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

lemma sum_sqrt_mono {a b : multiset ℕ} (h : one_step a b) :
  (a.map (sqrt ∘ coe)).sum ≤ (b.map (sqrt ∘ coe)).sum :=
begin
  induction h with x y m,
  simp,
  rw [←add_assoc],
  refine add_le_add_right (nnreal.sqrt_add_sqrt_le_sqrt_two_mul_add x y) _,
end

lemma sum_sqrt_mono_of_can_reach {a b : multiset ℕ} (h : can_reach a b) :
  (a.map (sqrt ∘ coe)).sum ≤ (b.map (sqrt ∘ coe)).sum :=
begin
  -- `apply` and `convert` infer the correct types, `refine` and `exact` don't
  convert mono_total_of_mono_step (λ m : multiset ℕ, (m.map (sqrt ∘ coe)).sum) @sum_sqrt_mono h
end

theorem week6_p2 {n r} (h : can_reach (multiset.Ico 1 (n + 1)) {r}) :
  (4 : ℝ≥0) / 9 * n^3 ≤ (r : ℝ≥0) :=
begin
  rw ←order_iso.le_iff_le sqrt,
  transitivity ((multiset.Ico 1 (n + 1)).map (sqrt ∘ coe)).sum,
  { exact le_sum_sqrt, },
  { convert sum_sqrt_mono_of_can_reach h,
    rw [multiset.map_singleton, multiset.sum_singleton], }
end
