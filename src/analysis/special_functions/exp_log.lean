/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import data.complex.exponential
import analysis.complex.basic

/-!
# Complex and real exponential, real logarithm

## Main statements

This file establishes the continuity of the complex and real exponential functions.

It also contains the definition of the real logarithm function (as the inverse of the
exponential on `(0, +∞)`, extended to `ℝ` by setting `log (-x) = log x`) and its continuity.

The complex logarithm is *not* defined in this file as it relies on trigonometric functions. See
instead `trigonometric_continuity.lean`.

## Tags

exp, log
-/

open metric filter finset function set
open_locale classical topological_space

variables {z y x : ℝ}

section continuity

namespace complex

lemma exp_bound_first_order (x z : ℂ) (hz : ∥z∥ ≤ 1) :
  ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2 :=
calc ∥exp (x + z) - exp x - z * exp x∥
    = ∥exp x * (exp z - 1 - z)∥ : by { congr, rw [exp_add], ring }
... = ∥exp x∥ * ∥exp z - 1 - z∥ : normed_field.norm_mul _ _
... ≤ ∥exp x∥ * ∥z∥^2 : mul_le_mul_of_nonneg_left (abs_exp_sub_one_sub_id_le hz) (norm_nonneg _)

@[continuity] lemma continuous_exp : continuous exp :=
begin
  refine continuous_iff.mpr (λ x ε hε_pos, _),
  simp_rw dist_eq_norm,
  have h_first_order : ∀ z, ∥z∥ ≤ 1 → ∥exp (x + z) - exp x∥ ≤ ∥z∥ * ∥exp x∥ + ∥exp x∥ * ∥z∥ ^ 2,
  { intros z hz,
    have : ∥exp (x + z) - exp x - z • exp x∥ ≤ ∥exp x∥ * ∥z∥ ^ 2, from exp_bound_first_order x z hz,
    rw [← sub_le_iff_le_add',  ← norm_smul z],
    exact (norm_sub_norm_le _ _).trans this, },
  -- introduce small enough `δ'`
  let δ' := min 1 ((ε/2) / (2 * ∥exp x∥)),
  have hδ'_right_pos : 0 < (ε/2) / (2 * ∥exp x∥),
    by { refine div_pos (half_pos hε_pos) _, simp [exp_ne_zero],},
  have hδ'_pos : 0 < δ',
    by { simp only [true_and, gt_iff_lt, lt_min_iff, zero_lt_one, hδ'_right_pos], },
  have hδ'_sq_le : δ' ^ 2 ≤ δ',
  { rw [← inv_le_inv hδ'_pos (sq_pos_of_ne_zero _ hδ'_pos.ne.symm), ← inv_pow'],
    nth_rewrite 0 ← pow_one δ'⁻¹,
    exact pow_le_pow (one_le_inv hδ'_pos (min_le_left _ _)) one_le_two, },
  refine ⟨δ', hδ'_pos, λ y hyδ', _⟩,
  have hy_eq : y = x + (y - x), by abel,
  have hyx_le_one : ∥y - x∥ ≤ 1, from hyδ'.le.trans (min_le_left _ _),
  -- now compute the difference, check that it is `< ε`
  calc ∥exp y - exp x∥
      = ∥exp (x + (y - x)) - exp x∥ : by nth_rewrite 0 hy_eq
  ... ≤ ∥y - x∥ * ∥exp x∥ + ∥exp x∥ * ∥y - x∥ ^ 2 : h_first_order (y - x) hyx_le_one
  ... ≤ δ' * ∥exp x∥ + ∥exp x∥ * δ' ^ 2 : begin
    refine add_le_add (mul_le_mul hyδ'.le le_rfl (norm_nonneg _) hδ'_pos.le)
      (mul_le_mul le_rfl (sq_le_sq _) (sq_nonneg _) (norm_nonneg _)),
    rw [abs_eq_self.mpr (norm_nonneg _), abs_eq_self.mpr hδ'_pos.le],
    exact hyδ'.le,
  end
  ... ≤ δ' * ∥exp x∥ + ∥exp x∥ * δ' :
    add_le_add le_rfl (mul_le_mul le_rfl hδ'_sq_le (sq_nonneg _) (norm_nonneg _))
  ... = δ' * (2 * ∥exp x∥) : by ring
  ... ≤ ((ε/2) / (2 * ∥exp x∥)) * (2 * ∥exp x∥) : begin
    simp_rw δ',
    exact mul_le_mul (min_le_right _ _) le_rfl (mul_nonneg zero_le_two (norm_nonneg _))
      hδ'_right_pos.le,
  end
  ... = ε / 2 : div_mul_cancel _ (mul_ne_zero two_ne_zero (by simp [exp_ne_zero]))
  ... < ε : half_lt_self hε_pos,
end

lemma continuous_on_exp {s : set ℂ} : continuous_on exp s :=
continuous_exp.continuous_on

end complex

namespace real

@[continuity] lemma continuous_exp : continuous exp :=
complex.continuous_re.comp (complex.continuous_exp.comp complex.continuous_of_real)

lemma continuous_on_exp {s : set ℝ} : continuous_on exp s :=
continuous_exp.continuous_on

end real

end continuity


namespace real

section tendsto_exp

/-- The real exponential function tends to `+∞` at `+∞`. -/
lemma tendsto_exp_at_top : tendsto exp at_top at_top :=
begin
  have A : tendsto (λx:ℝ, x + 1) at_top at_top :=
    tendsto_at_top_add_const_right at_top 1 tendsto_id,
  have B : ∀ᶠ x in at_top, x + 1 ≤ exp x :=
    eventually_at_top.2 ⟨0, λx hx, add_one_le_exp_of_nonneg hx⟩,
  exact tendsto_at_top_mono' at_top B A
end

/-- The real exponential function tends to `0` at `-∞` or, equivalently, `exp(-x)` tends to `0`
at `+∞` -/
lemma tendsto_exp_neg_at_top_nhds_0 : tendsto (λx, exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp tendsto_exp_at_top).congr (λx, (exp_neg x).symm)

/-- The real exponential function tends to `1` at `0`. -/
lemma tendsto_exp_nhds_0_nhds_1 : tendsto exp (𝓝 0) (𝓝 1) :=
by { convert continuous_exp.tendsto 0, simp }

lemma tendsto_exp_at_bot : tendsto exp at_bot (𝓝 0) :=
(tendsto_exp_neg_at_top_nhds_0.comp tendsto_neg_at_bot_at_top).congr $
  λ x, congr_arg exp $ neg_neg x

lemma tendsto_exp_at_bot_nhds_within : tendsto exp at_bot (𝓝[Ioi 0] 0) :=
tendsto_inf.2 ⟨tendsto_exp_at_bot, tendsto_principal.2 $ eventually_of_forall exp_pos⟩

end tendsto_exp

section real_exp_order_iso

/-- `real.exp` as an order isomorphism between `ℝ` and `(0, +∞)`. -/
noncomputable def exp_order_iso : ℝ ≃o Ioi (0 : ℝ) :=
strict_mono.order_iso_of_surjective _ (exp_strict_mono.cod_restrict exp_pos) $
  (continuous_subtype_mk _ continuous_exp).surjective
    (by simp only [tendsto_Ioi_at_top, subtype.coe_mk, tendsto_exp_at_top])
    (by simp [tendsto_exp_at_bot_nhds_within])

@[simp] lemma coe_exp_order_iso_apply (x : ℝ) : (exp_order_iso x : ℝ) = exp x := rfl

@[simp] lemma coe_comp_exp_order_iso : coe ∘ exp_order_iso = exp := rfl

@[simp] lemma range_exp : range exp = Ioi 0 :=
by rw [← coe_comp_exp_order_iso, range_comp, exp_order_iso.range_eq, image_univ, subtype.range_coe]

@[simp] lemma map_exp_at_top : map exp at_top = at_top :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, order_iso.map_at_top, map_coe_Ioi_at_top]

@[simp] lemma comap_exp_at_top : comap exp at_top = at_top :=
by rw [← map_exp_at_top, comap_map exp_injective, map_exp_at_top]

@[simp] lemma tendsto_exp_comp_at_top {α : Type*} {l : filter α} {f : α → ℝ} :
  tendsto (λ x, exp (f x)) l at_top ↔ tendsto f l at_top :=
by rw [← tendsto_comap_iff, comap_exp_at_top]

lemma tendsto_comp_exp_at_top {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_top l ↔ tendsto f at_top l :=
by rw [← tendsto_map'_iff, map_exp_at_top]

@[simp] lemma map_exp_at_bot : map exp at_bot = 𝓝[Ioi 0] 0 :=
by rw [← coe_comp_exp_order_iso, ← filter.map_map, exp_order_iso.map_at_bot, ← map_coe_Ioi_at_bot]

lemma comap_exp_nhds_within_Ioi_zero : comap exp (𝓝[Ioi 0] 0) = at_bot :=
by rw [← map_exp_at_bot, comap_map exp_injective]

lemma tendsto_comp_exp_at_bot {α : Type*} {l : filter α} {f : ℝ → α} :
  tendsto (λ x, f (exp x)) at_bot l ↔ tendsto f (𝓝[Ioi 0] 0) l :=
by rw [← map_exp_at_bot, tendsto_map'_iff]

end real_exp_order_iso

end real



namespace real

/-- The real logarithm function, equal to the inverse of the exponential for `x > 0`,
to `log |x|` for `x < 0`, and to `0` for `0`. We use this unconventional extension to
`(-∞, 0]` as it gives the formula `log (x * y) = log x + log y` for all nonzero `x` and `y`, and
the derivative of `log` is `1/x` away from `0`. -/
@[pp_nodot] noncomputable def log (x : ℝ) : ℝ :=
if hx : x = 0 then 0 else exp_order_iso.symm ⟨abs x, abs_pos.2 hx⟩

lemma log_of_ne_zero (hx : x ≠ 0) : log x = exp_order_iso.symm ⟨abs x, abs_pos.2 hx⟩ := dif_neg hx

lemma log_of_pos (hx : 0 < x) : log x = exp_order_iso.symm ⟨x, hx⟩ :=
by { rw [log_of_ne_zero hx.ne'], congr, exact abs_of_pos hx }

lemma exp_log_eq_abs (hx : x ≠ 0) : exp (log x) = abs x :=
by rw [log_of_ne_zero hx, ← coe_exp_order_iso_apply, order_iso.apply_symm_apply, subtype.coe_mk]

lemma exp_log (hx : 0 < x) : exp (log x) = x :=
by { rw exp_log_eq_abs hx.ne', exact abs_of_pos hx }

lemma exp_log_of_neg (hx : x < 0) : exp (log x) = -x :=
by { rw exp_log_eq_abs (ne_of_lt hx), exact abs_of_neg hx }

@[simp] lemma log_exp (x : ℝ) : log (exp x) = x :=
exp_injective $ exp_log (exp_pos x)

lemma surj_on_log : surj_on log (Ioi 0) univ :=
λ x _, ⟨exp x, exp_pos x, log_exp x⟩

lemma log_surjective : surjective log :=
λ x, ⟨exp x, log_exp x⟩

@[simp] lemma range_log : range log = univ :=
log_surjective.range_eq

@[simp] lemma log_zero : log 0 = 0 := dif_pos rfl

@[simp] lemma log_one : log 1 = 0 :=
exp_injective $ by rw [exp_log zero_lt_one, exp_zero]

@[simp] lemma log_abs (x : ℝ) : log (abs x) = log x :=
begin
  by_cases h : x = 0,
  { simp [h] },
  { rw [← exp_eq_exp, exp_log_eq_abs h, exp_log_eq_abs (abs_pos.2 h).ne', abs_abs] }
end

@[simp] lemma log_neg_eq_log (x : ℝ) : log (-x) = log x :=
by rw [← log_abs x, ← log_abs (-x), abs_neg]

lemma surj_on_log' : surj_on log (Iio 0) univ :=
λ x _, ⟨-exp x, neg_lt_zero.2 $ exp_pos x, by rw [log_neg_eq_log, log_exp]⟩

lemma log_mul (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=
exp_injective $
by rw [exp_log_eq_abs (mul_ne_zero hx hy), exp_add, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_mul]

lemma log_div (hx : x ≠ 0) (hy : y ≠ 0) : log (x / y) = log x - log y :=
exp_injective $
by rw [exp_log_eq_abs (div_ne_zero hx hy), exp_sub, exp_log_eq_abs hx, exp_log_eq_abs hy, abs_div]

@[simp] lemma log_inv (x : ℝ) : log (x⁻¹) = -log x :=
begin
  by_cases hx : x = 0, { simp [hx] },
  rw [← exp_eq_exp, exp_log_eq_abs (inv_ne_zero hx), exp_neg, exp_log_eq_abs hx, abs_inv]
end

lemma log_le_log (h : 0 < x) (h₁ : 0 < y) : real.log x ≤ real.log y ↔ x ≤ y :=
by rw [← exp_le_exp, exp_log h, exp_log h₁]

lemma log_lt_log (hx : 0 < x) : x < y → log x < log y :=
by { intro h, rwa [← exp_lt_exp, exp_log hx, exp_log (lt_trans hx h)] }

lemma log_lt_log_iff (hx : 0 < x) (hy : 0 < y) : log x < log y ↔ x < y :=
by { rw [← exp_lt_exp, exp_log hx, exp_log hy] }

lemma log_pos_iff (hx : 0 < x) : 0 < log x ↔ 1 < x :=
by { rw ← log_one, exact log_lt_log_iff zero_lt_one hx }

lemma log_pos (hx : 1 < x) : 0 < log x :=
(log_pos_iff (lt_trans zero_lt_one hx)).2 hx

lemma log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1 :=
by { rw ← log_one, exact log_lt_log_iff h zero_lt_one }

lemma log_neg (h0 : 0 < x) (h1 : x < 1) : log x < 0 := (log_neg_iff h0).2 h1

lemma log_nonneg_iff (hx : 0 < x) : 0 ≤ log x ↔ 1 ≤ x :=
by rw [← not_lt, log_neg_iff hx, not_lt]

lemma log_nonneg (hx : 1 ≤ x) : 0 ≤ log x :=
(log_nonneg_iff (zero_lt_one.trans_le hx)).2 hx

lemma log_nonpos_iff (hx : 0 < x) : log x ≤ 0 ↔ x ≤ 1 :=
by rw [← not_lt, log_pos_iff hx, not_lt]

lemma log_nonpos_iff' (hx : 0 ≤ x) : log x ≤ 0 ↔ x ≤ 1 :=
begin
  rcases hx.eq_or_lt with (rfl|hx),
  { simp [le_refl, zero_le_one] },
  exact log_nonpos_iff hx
end

lemma log_nonpos (hx : 0 ≤ x) (h'x : x ≤ 1) : log x ≤ 0 :=
(log_nonpos_iff' hx).2 h'x

lemma strict_mono_incr_on_log : strict_mono_incr_on log (set.Ioi 0) :=
λ x hx y hy hxy, log_lt_log hx hxy

lemma strict_mono_decr_on_log : strict_mono_decr_on log (set.Iio 0) :=
begin
  rintros x (hx : x < 0) y (hy : y < 0) hxy,
  rw [← log_abs y, ← log_abs x],
  refine log_lt_log (abs_pos.2 hy.ne) _,
  rwa [abs_of_neg hy, abs_of_neg hx, neg_lt_neg_iff]
end

lemma log_inj_on_pos : set.inj_on log (set.Ioi 0) :=
strict_mono_incr_on_log.inj_on

lemma eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
log_inj_on_pos (set.mem_Ioi.2 h₁) (set.mem_Ioi.2 zero_lt_one) (h₂.trans real.log_one.symm)

lemma log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx

/-- The real logarithm function tends to `+∞` at `+∞`. -/
lemma tendsto_log_at_top : tendsto log at_top at_top :=
tendsto_comp_exp_at_top.1 $ by simpa only [log_exp] using tendsto_id

lemma tendsto_log_nhds_within_zero : tendsto log (𝓝[{0}ᶜ] 0) at_bot :=
begin
  rw [← (show _ = log, from funext log_abs)],
  refine tendsto.comp _ tendsto_abs_nhds_within_zero,
  simpa [← tendsto_comp_exp_at_bot] using tendsto_id
end

lemma continuous_on_log : continuous_on log {0}ᶜ :=
begin
  rw [continuous_on_iff_continuous_restrict, restrict],
  conv in (log _) { rw [log_of_ne_zero (show (x : ℝ) ≠ 0, from x.2)] },
  exact exp_order_iso.symm.continuous.comp (continuous_subtype_mk _ continuous_subtype_coe.norm)
end

@[continuity] lemma continuous_log : continuous (λ x : {x : ℝ // x ≠ 0}, log x) :=
continuous_on_iff_continuous_restrict.1 $ continuous_on_log.mono $ λ x hx, hx

@[continuity] lemma continuous_log' : continuous (λ x : {x : ℝ // 0 < x}, log x) :=
continuous_on_iff_continuous_restrict.1 $ continuous_on_log.mono $ λ x hx, ne_of_gt hx

lemma continuous_at_log (hx : x ≠ 0) : continuous_at log x :=
(continuous_on_log x hx).continuous_at $ is_open.mem_nhds is_open_compl_singleton hx

@[simp] lemma continuous_at_log_iff : continuous_at log x ↔ x ≠ 0 :=
begin
  refine ⟨_, continuous_at_log⟩,
  rintros h rfl,
  exact not_tendsto_nhds_of_tendsto_at_bot tendsto_log_nhds_within_zero _
    (h.tendsto.mono_left inf_le_left)
end

end real

section continuity
open real

variables {α : Type*}

lemma filter.tendsto.log {f : α → ℝ} {l : filter α} {x : ℝ} (h : tendsto f l (𝓝 x)) (hx : x ≠ 0) :
  tendsto (λ x, log (f x)) l (𝓝 (log x)) :=
(continuous_at_log hx).tendsto.comp h

variables [topological_space α] {f : α → ℝ} {s : set α} {a : α}

lemma continuous.log (hf : continuous f) (h₀ : ∀ x, f x ≠ 0) : continuous (λ x, log (f x)) :=
continuous_on_log.comp_continuous hf h₀

lemma continuous_at.log (hf : continuous_at f a) (h₀ : f a ≠ 0) :
  continuous_at (λ x, log (f x)) a :=
hf.log h₀

lemma continuous_within_at.log (hf : continuous_within_at f s a) (h₀ : f a ≠ 0) :
  continuous_within_at (λ x, log (f x)) s a :=
hf.log h₀

lemma continuous_on.log (hf : continuous_on f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
  continuous_on (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (h₀ x hx)

end continuity
