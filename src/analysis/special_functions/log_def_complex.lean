import analysis.special_functions.exp_log_continuity

open filter set real

namespace complex

/-- Inverse of the `exp` function. Returns values such that `(log x).im > - π` and `(log x).im ≤ π`.
  `log 0 = 0`-/
@[pp_nodot] noncomputable def log (x : ℂ) : ℂ := x.abs.log + arg x * I

lemma log_re (x : ℂ) : x.log.re = x.abs.log := by simp [log]

lemma log_im (x : ℂ) : x.log.im = x.arg := by simp [log]

lemma neg_pi_lt_log_im (x : ℂ) : -π < (log x).im := by simp only [log_im, neg_pi_lt_arg]
lemma log_im_le_pi (x : ℂ) : (log x).im ≤ π := by simp only [log_im, arg_le_pi]

lemma exp_log {x : ℂ} (hx : x ≠ 0) : exp (log x) = x :=
by rw [log, exp_add_mul_I, ← of_real_sin, sin_arg, ← of_real_cos, cos_arg hx,
  ← of_real_exp, real.exp_log (abs_pos.2 hx), mul_add, of_real_div, of_real_div,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), ← mul_assoc,
  mul_div_cancel' _ (of_real_ne_zero.2 (mt abs_eq_zero.1 hx)), re_add_im]

lemma range_exp : range exp = {x | x ≠ 0} :=
set.ext $ λ x, ⟨by { rintro ⟨x, rfl⟩, exact exp_ne_zero x }, λ hx, ⟨log x, exp_log hx⟩⟩

lemma exp_inj_of_neg_pi_lt_of_le_pi {x y : ℂ} (hx₁ : -π < x.im) (hx₂ : x.im ≤ π)
  (hy₁ : - π < y.im) (hy₂ : y.im ≤ π) (hxy : exp x = exp y) : x = y :=
by rw [exp_eq_exp_re_mul_sin_add_cos, exp_eq_exp_re_mul_sin_add_cos y] at hxy;
  exact complex.ext
    (real.exp_injective $
      by simpa [abs_mul, abs_cos_add_sin_mul_I] using congr_arg complex.abs hxy)
    (by simpa [(of_real_exp _).symm, - of_real_exp, arg_real_mul _ (real.exp_pos _),
      arg_cos_add_sin_mul_I hx₁ hx₂, arg_cos_add_sin_mul_I hy₁ hy₂] using congr_arg arg hxy)

lemma log_exp {x : ℂ} (hx₁ : -π < x.im) (hx₂: x.im ≤ π) : log (exp x) = x :=
exp_inj_of_neg_pi_lt_of_le_pi
  (by rw log_im; exact neg_pi_lt_arg _)
  (by rw log_im; exact arg_le_pi _)
  hx₁ hx₂ (by rw [exp_log (exp_ne_zero _)])

lemma of_real_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
complex.ext
  (by rw [log_re, of_real_re, abs_of_nonneg hx])
  (by rw [of_real_im, log_im, arg_of_real_of_nonneg hx])

lemma log_of_real_re (x : ℝ) : (log (x : ℂ)).re = real.log x := by simp [log_re]

@[simp] lemma log_zero : log 0 = 0 := by simp [log]

@[simp] lemma log_one : log 1 = 0 := by simp [log]

lemma log_neg_one : log (-1) = π * I := by simp [log]

lemma log_I : log I = π / 2 * I := by simp [log]

lemma log_neg_I : log (-I) = -(π / 2) * I := by simp [log]



end complex
