/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/
import analysis.calculus.inverse
import analysis.complex.real_deriv
import analysis.special_functions.exp_log_continuity

/-!
# Complex and real exponential, real logarithm

## Main statements

This file establishes the basic analytical properties of the complex and real exponential functions
(continuity, differentiability, computation of the derivative).

It also contains the definition of the real logarithm function (as the inverse of the
exponential on `(0, +∞)`, extended to `ℝ` by setting `log (-x) = log x`) and its basic
properties (continuity, differentiability, formula for the derivative).

The complex logarithm is *not* defined in this file as it relies on trigonometric functions. See
instead `trigonometric.lean`.

## Tags

exp, log
-/

noncomputable theory

open finset filter metric asymptotics set function
open_locale classical topological_space

namespace complex

/-- The complex exponential is everywhere differentiable, with the derivative `exp x`. -/
lemma has_deriv_at_exp (x : ℂ) : has_deriv_at exp (exp x) x :=
begin
  rw has_deriv_at_iff_is_o_nhds_zero,
  have : (1 : ℕ) < 2 := by norm_num,
  refine (is_O.of_bound (∥exp x∥) _).trans_is_o (is_o_pow_id this),
  filter_upwards [metric.ball_mem_nhds (0 : ℂ) zero_lt_one],
  simp only [metric.mem_ball, dist_zero_right, normed_field.norm_pow],
  exact λ z hz, exp_bound_first_order x z hz.le,
end

lemma differentiable_exp : differentiable ℂ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp {x : ℂ} : differentiable_at ℂ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

lemma times_cont_diff_exp : ∀ {n}, times_cont_diff ℂ n exp :=
begin
  refine times_cont_diff_all_iff_nat.2 (λ n, _),
  induction n with n ihn,
  { exact times_cont_diff_zero.2 continuous_exp },
  { rw times_cont_diff_succ_iff_deriv,
    use differentiable_exp,
    rwa deriv_exp }
end

lemma has_strict_deriv_at_exp (x : ℂ) : has_strict_deriv_at exp (exp x) x :=
times_cont_diff_exp.times_cont_diff_at.has_strict_deriv_at' (has_deriv_at_exp x) le_rfl

lemma is_open_map_exp : is_open_map exp :=
open_map_of_strict_deriv has_strict_deriv_at_exp exp_ne_zero

end complex

section
variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

lemma has_strict_deriv_at.cexp (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_strict_deriv_at_exp (f x)).comp x hf

lemma has_deriv_at.cexp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') x :=
(complex.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.cexp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) * f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cexp (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.exp (f x)) s x = complex.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cexp.deriv_within hxs

@[simp] lemma deriv_cexp (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.exp (f x)) x = complex.exp (f x) * (deriv f x) :=
hc.has_deriv_at.cexp.deriv

end

section

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

lemma has_strict_fderiv_at.cexp (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') x :=
(complex.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_within_at.cexp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') s x :=
(complex.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.cexp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.exp (f x)) (complex.exp (f x) • f') x :=
has_fderiv_within_at_univ.1 $ hf.has_fderiv_within_at.cexp

lemma differentiable_within_at.cexp (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.exp (f x)) s x :=
hf.has_fderiv_within_at.cexp.differentiable_within_at

@[simp] lemma differentiable_at.cexp (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.exp (f x)) x :=
hc.has_fderiv_at.cexp.differentiable_at

lemma differentiable_on.cexp (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.exp (f x)) s :=
λx h, (hc x h).cexp

@[simp] lemma differentiable.cexp (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.exp (f x)) :=
λx, (hc x).cexp

lemma times_cont_diff.cexp {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.exp (f x)) :=
complex.times_cont_diff_exp.comp h

lemma times_cont_diff_at.cexp {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.exp (f x)) x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cexp {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.exp (f x)) s :=
complex.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cexp {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.exp (f x)) s x :=
complex.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_exp (x : ℝ) : has_strict_deriv_at exp (exp x) x :=
(complex.has_strict_deriv_at_exp x).real_of_complex

lemma has_deriv_at_exp (x : ℝ) : has_deriv_at exp (exp x) x :=
(complex.has_deriv_at_exp x).real_of_complex

lemma times_cont_diff_exp {n} : times_cont_diff ℝ n exp :=
complex.times_cont_diff_exp.real_of_complex

lemma differentiable_exp : differentiable ℝ exp :=
λx, (has_deriv_at_exp x).differentiable_at

lemma differentiable_at_exp : differentiable_at ℝ exp x :=
differentiable_exp x

@[simp] lemma deriv_exp : deriv exp = exp :=
funext $ λ x, (has_deriv_at_exp x).deriv

@[simp] lemma iter_deriv_exp : ∀ n : ℕ, (deriv^[n] exp) = exp
| 0 := rfl
| (n+1) := by rw [iterate_succ_apply, deriv_exp, iter_deriv_exp n]

end real


section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_strict_deriv_at.exp (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_strict_deriv_at_exp (f x)).comp x hf

lemma has_deriv_at.exp (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.exp (f x)) (real.exp (f x) * f') x :=
(real.has_deriv_at_exp (f x)).comp x hf

lemma has_deriv_within_at.exp (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.exp (f x)) (real.exp (f x) * f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.exp (f x)) s x = real.exp (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.exp.deriv_within hxs

@[simp] lemma deriv_exp (hc : differentiable_at ℝ f x) :
  deriv (λx, real.exp (f x)) x = real.exp (f x) * (deriv f x) :=
hc.has_deriv_at.exp.deriv

end

section
/-! Register lemmas for the derivatives of the composition of `real.exp` with a differentiable
function, for standalone use and use with `simp`. -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

lemma times_cont_diff.exp {n} (hf : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.exp (f x)) :=
real.times_cont_diff_exp.comp hf

lemma times_cont_diff_at.exp {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.exp (f x)) x :=
real.times_cont_diff_exp.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.exp {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.exp (f x)) s :=
real.times_cont_diff_exp.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.exp {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.exp (f x)) s x :=
real.times_cont_diff_exp.times_cont_diff_at.comp_times_cont_diff_within_at x hf

lemma has_fderiv_within_at.exp (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.exp (f x)) (real.exp (f x) • f') s x :=
(real.has_deriv_at_exp (f x)).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.exp (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.exp (f x)) (real.exp (f x) • f') x :=
(real.has_deriv_at_exp (f x)).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.exp (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.exp (f x)) (real.exp (f x) • f') x :=
(real.has_strict_deriv_at_exp (f x)).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.exp (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.exp (f x)) s x :=
hf.has_fderiv_within_at.exp.differentiable_within_at

@[simp] lemma differentiable_at.exp (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.exp (f x)) x :=
hc.has_fderiv_at.exp.differentiable_at

lemma differentiable_on.exp (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.exp (f x)) s :=
λ x h, (hc x h).exp

@[simp] lemma differentiable.exp (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.exp (f x)) :=
λ x, (hc x).exp

lemma fderiv_within_exp (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.exp (f x)) s x = real.exp (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.exp.fderiv_within hxs

@[simp] lemma fderiv_exp (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.exp (f x)) x = real.exp (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.exp.fderiv

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_log_of_pos (hx : 0 < x) : has_strict_deriv_at log x⁻¹ x :=
have has_strict_deriv_at log (exp $ log x)⁻¹ x,
from (has_strict_deriv_at_exp $ log x).of_local_left_inverse (continuous_at_log hx.ne')
  (ne_of_gt $ exp_pos _) $ eventually.mono (lt_mem_nhds hx) @exp_log,
by rwa [exp_log hx] at this

lemma has_strict_deriv_at_log (hx : x ≠ 0) : has_strict_deriv_at log x⁻¹ x :=
begin
  cases hx.lt_or_lt with hx hx,
  { convert (has_strict_deriv_at_log_of_pos (neg_pos.mpr hx)).comp x (has_strict_deriv_at_neg x),
    { ext y, exact (log_neg_eq_log y).symm },
    { field_simp [hx.ne] } },
  { exact has_strict_deriv_at_log_of_pos hx }
end

lemma has_deriv_at_log (hx : x ≠ 0) : has_deriv_at log x⁻¹ x :=
(has_strict_deriv_at_log hx).has_deriv_at

lemma differentiable_at_log (hx : x ≠ 0) : differentiable_at ℝ log x :=
(has_deriv_at_log hx).differentiable_at

lemma differentiable_on_log : differentiable_on ℝ log {0}ᶜ :=
λ x hx, (differentiable_at_log hx).differentiable_within_at

@[simp] lemma differentiable_at_log_iff : differentiable_at ℝ log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at, differentiable_at_log⟩

lemma deriv_log (x : ℝ) : deriv log x = x⁻¹ :=
if hx : x = 0 then
  by rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_log_iff.1 (not_not.2 hx)), hx,
    inv_zero]
else (has_deriv_at_log hx).deriv

@[simp] lemma deriv_log' : deriv log = has_inv.inv := funext deriv_log

lemma times_cont_diff_on_log {n : with_top ℕ} : times_cont_diff_on ℝ n log {0}ᶜ :=
begin
  suffices : times_cont_diff_on ℝ ⊤ log {0}ᶜ, from this.of_le le_top,
  refine (times_cont_diff_on_top_iff_deriv_of_open is_open_compl_singleton).2 _,
  simp [differentiable_on_log, times_cont_diff_on_inv]
end

lemma times_cont_diff_at_log {n : with_top ℕ} : times_cont_diff_at ℝ n log x ↔ x ≠ 0 :=
⟨λ h, continuous_at_log_iff.1 h.continuous_at,
  λ hx, (times_cont_diff_on_log x hx).times_cont_diff_at $
    is_open.mem_nhds is_open_compl_singleton hx⟩

end real

section log_differentiable
open real

section deriv

variables {f : ℝ → ℝ} {x f' : ℝ} {s : set ℝ}

lemma has_deriv_within_at.log (hf : has_deriv_within_at f f' s x) (hx : f x ≠ 0) :
  has_deriv_within_at (λ y, log (f y)) (f' / (f x)) s x :=
begin
  rw div_eq_inv_mul,
  exact (has_deriv_at_log hx).comp_has_deriv_within_at x hf
end

lemma has_deriv_at.log (hf : has_deriv_at f f' x) (hx : f x ≠ 0) :
  has_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw ← has_deriv_within_at_univ at *,
  exact hf.log hx
end

lemma has_strict_deriv_at.log (hf : has_strict_deriv_at f f' x) (hx : f x ≠ 0) :
  has_strict_deriv_at (λ y, log (f y)) (f' / f x) x :=
begin
  rw div_eq_inv_mul,
  exact (has_strict_deriv_at_log hx).comp x hf
end

lemma deriv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, log (f x)) s x = (deriv_within f s x) / (f x) :=
(hf.has_deriv_within_at.log hx).deriv_within hxs

@[simp] lemma deriv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  deriv (λx, log (f x)) x = (deriv f x) / (f x) :=
(hf.has_deriv_at.log hx).deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
  {s : set E}

lemma has_fderiv_within_at.log (hf : has_fderiv_within_at f f' s x) (hx : f x ≠ 0) :
  has_fderiv_within_at (λ x, log (f x)) ((f x)⁻¹ • f') s x :=
(has_deriv_at_log hx).comp_has_fderiv_within_at x hf

lemma has_fderiv_at.log (hf : has_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_deriv_at_log hx).comp_has_fderiv_at x hf

lemma has_strict_fderiv_at.log (hf : has_strict_fderiv_at f f' x) (hx : f x ≠ 0) :
  has_strict_fderiv_at (λ x, log (f x)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log hx).comp_has_strict_fderiv_at x hf

lemma differentiable_within_at.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0) :
  differentiable_within_at ℝ (λx, log (f x)) s x :=
(hf.has_fderiv_within_at.log hx).differentiable_within_at

@[simp] lemma differentiable_at.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  differentiable_at ℝ (λx, log (f x)) x :=
(hf.has_fderiv_at.log hx).differentiable_at

lemma times_cont_diff_at.log {n} (hf : times_cont_diff_at ℝ n f x) (hx : f x ≠ 0) :
  times_cont_diff_at ℝ n (λ x, log (f x)) x :=
(times_cont_diff_at_log.2 hx).comp x hf

lemma times_cont_diff_within_at.log {n} (hf : times_cont_diff_within_at ℝ n f s x) (hx : f x ≠ 0) :
  times_cont_diff_within_at ℝ n (λ x, log (f x)) s x :=
(times_cont_diff_at_log.2 hx).comp_times_cont_diff_within_at x hf

lemma times_cont_diff_on.log {n} (hf : times_cont_diff_on ℝ n f s) (hs : ∀ x ∈ s, f x ≠ 0) :
  times_cont_diff_on ℝ n (λ x, log (f x)) s :=
λ x hx, (hf x hx).log (hs x hx)

lemma times_cont_diff.log {n} (hf : times_cont_diff ℝ n f) (h : ∀ x, f x ≠ 0) :
  times_cont_diff ℝ n (λ x, log (f x)) :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x, hf.times_cont_diff_at.log (h x)

lemma differentiable_on.log (hf : differentiable_on ℝ f s) (hx : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λx, log (f x)) s :=
λx h, (hf x h).log (hx x h)

@[simp] lemma differentiable.log (hf : differentiable ℝ f) (hx : ∀ x, f x ≠ 0) :
  differentiable ℝ (λx, log (f x)) :=
λx, (hf x).log (hx x)

lemma fderiv_within.log (hf : differentiable_within_at ℝ f s x) (hx : f x ≠ 0)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, log (f x)) s x = (f x)⁻¹ • fderiv_within ℝ f s x :=
(hf.has_fderiv_within_at.log hx).fderiv_within hxs

@[simp] lemma fderiv.log (hf : differentiable_at ℝ f x) (hx : f x ≠ 0) :
  fderiv ℝ (λx, log (f x)) x = (f x)⁻¹ • fderiv ℝ f x :=
(hf.has_fderiv_at.log hx).fderiv

end fderiv

end log_differentiable

namespace real

/-- The function `exp(x)/x^n` tends to `+∞` at `+∞`, for any natural number `n` -/
lemma tendsto_exp_div_pow_at_top (n : ℕ) : tendsto (λx, exp x / x^n) at_top at_top :=
begin
  refine (at_top_basis_Ioi.tendsto_iff (at_top_basis' 1)).2 (λ C hC₁, _),
  have hC₀ : 0 < C, from zero_lt_one.trans_le hC₁,
  have : 0 < (exp 1 * C)⁻¹ := inv_pos.2 (mul_pos (exp_pos _) hC₀),
  obtain ⟨N, hN⟩ : ∃ N, ∀ k ≥ N, (↑k ^ n : ℝ) / exp 1 ^ k < (exp 1 * C)⁻¹ :=
    eventually_at_top.1 ((tendsto_pow_const_div_const_pow_of_one_lt n
      (one_lt_exp_iff.2 zero_lt_one)).eventually (gt_mem_nhds this)),
  simp only [← exp_nat_mul, mul_one, div_lt_iff, exp_pos, ← div_eq_inv_mul] at hN,
  refine ⟨N, trivial, λ x hx, _⟩, rw mem_Ioi at hx,
  have hx₀ : 0 < x, from N.cast_nonneg.trans_lt hx,
  rw [mem_Ici, le_div_iff (pow_pos hx₀ _), ← le_div_iff' hC₀],
  calc x ^ n ≤ ⌈x⌉₊ ^ n : pow_le_pow_of_le_left hx₀.le (le_nat_ceil _) _
  ... ≤ exp ⌈x⌉₊ / (exp 1 * C) : (hN _ (lt_nat_ceil.2 hx).le).le
  ... ≤ exp (x + 1) / (exp 1 * C) : div_le_div_of_le (mul_pos (exp_pos _) hC₀).le
    (exp_le_exp.2 $ (nat_ceil_lt_add_one hx₀.le).le)
  ... = exp x / C : by rw [add_comm, exp_add, mul_div_mul_left _ _ (exp_pos _).ne']
end

/-- The function `x^n * exp(-x)` tends to `0` at `+∞`, for any natural number `n`. -/
lemma tendsto_pow_mul_exp_neg_at_top_nhds_0 (n : ℕ) : tendsto (λx, x^n * exp (-x)) at_top (𝓝 0) :=
(tendsto_inv_at_top_zero.comp (tendsto_exp_div_pow_at_top n)).congr $ λx,
  by rw [comp_app, inv_eq_one_div, div_div_eq_mul_div, one_mul, div_eq_mul_inv, exp_neg]

/-- The function `(b * exp x + c) / (x ^ n)` tends to `+∞` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is positive. -/
lemma tendsto_mul_exp_add_div_pow_at_top (b c : ℝ) (n : ℕ) (hb : 0 < b) (hn : 1 ≤ n) :
  tendsto (λ x, (b * (exp x) + c) / (x^n)) at_top at_top :=
begin
  refine tendsto.congr' (eventually_eq_of_mem (Ioi_mem_at_top 0) _)
    (((tendsto_exp_div_pow_at_top n).const_mul_at_top hb).at_top_add
      ((tendsto_pow_neg_at_top hn).mul (@tendsto_const_nhds _ _ _ c _))),
  intros x hx,
  simp only [fpow_neg x n],
  ring,
end

/-- The function `(x ^ n) / (b * exp x + c)` tends to `0` at `+∞`, for any positive natural number
`n` and any real numbers `b` and `c` such that `b` is nonzero. -/
lemma tendsto_div_pow_mul_exp_add_at_top (b c : ℝ) (n : ℕ) (hb : 0 ≠ b) (hn : 1 ≤ n) :
  tendsto (λ x, x^n / (b * (exp x) + c)) at_top (𝓝 0) :=
begin
  have H : ∀ d e, 0 < d → tendsto (λ (x:ℝ), x^n / (d * (exp x) + e)) at_top (𝓝 0),
  { intros b' c' h,
    convert (tendsto_mul_exp_add_div_pow_at_top b' c' n h hn).inv_tendsto_at_top ,
    ext x,
    simpa only [pi.inv_apply] using inv_div.symm },
  cases lt_or_gt_of_ne hb,
  { exact H b c h },
  { convert (H (-b) (-c) (neg_pos.mpr h)).neg,
    { ext x,
      field_simp,
      rw [← neg_add (b * exp x) c, neg_div_neg_eq] },
    { exact neg_zero.symm } },
end

/-- The function `x * log (1 + t / x)` tends to `t` at `+∞`. -/
lemma tendsto_mul_log_one_plus_div_at_top (t : ℝ) :
  tendsto (λ x, x * log (1 + t / x)) at_top (𝓝 t) :=
begin
  have h₁ : tendsto (λ h, h⁻¹ * log (1 + t * h)) (𝓝[{0}ᶜ] 0) (𝓝 t),
  { simpa [has_deriv_at_iff_tendsto_slope] using
      ((has_deriv_at_const _ 1).add ((has_deriv_at_id (0 : ℝ)).const_mul t)).log (by simp) },
  have h₂ : tendsto (λ x : ℝ, x⁻¹) at_top (𝓝[{0}ᶜ] 0) :=
    tendsto_inv_at_top_zero'.mono_right (nhds_within_mono _ (λ x hx, (set.mem_Ioi.mp hx).ne')),
  convert h₁.comp h₂,
  ext,
  field_simp [mul_comm],
end

open_locale big_operators

/-- A crude lemma estimating the difference between `log (1-x)` and its Taylor series at `0`,
where the main point of the bound is that it tends to `0`. The goal is to deduce the series
expansion of the logarithm, in `has_sum_pow_div_log_of_abs_lt_1`.
-/
lemma abs_log_sub_add_sum_range_le {x : ℝ} (h : abs x < 1) (n : ℕ) :
  abs ((∑ i in range n, x^(i+1)/(i+1)) + log (1-x)) ≤ (abs x)^(n+1) / (1 - abs x) :=
begin
  /- For the proof, we show that the derivative of the function to be estimated is small,
  and then apply the mean value inequality. -/
  let F : ℝ → ℝ := λ x, ∑ i in range n, x^(i+1)/(i+1) + log (1-x),
  -- First step: compute the derivative of `F`
  have A : ∀ y ∈ Ioo (-1 : ℝ) 1, deriv F y = - (y^n) / (1 - y),
  { assume y hy,
    have : (∑ i in range n, (↑i + 1) * y ^ i / (↑i + 1)) = (∑ i in range n, y ^ i),
    { congr' with i,
      have : (i : ℝ) + 1 ≠ 0 := ne_of_gt (nat.cast_add_one_pos i),
      field_simp [this, mul_comm] },
    field_simp [F, this, ← geom_sum_def, geom_sum_eq (ne_of_lt hy.2),
                sub_ne_zero_of_ne (ne_of_gt hy.2), sub_ne_zero_of_ne (ne_of_lt hy.2)],
    ring },
  -- second step: show that the derivative of `F` is small
  have B : ∀ y ∈ Icc (-abs x) (abs x), abs (deriv F y) ≤ (abs x)^n / (1 - abs x),
  { assume y hy,
    have : y ∈ Ioo (-(1 : ℝ)) 1 := ⟨lt_of_lt_of_le (neg_lt_neg h) hy.1, lt_of_le_of_lt hy.2 h⟩,
    calc abs (deriv F y) = abs (-(y^n) / (1 - y)) : by rw [A y this]
    ... ≤ (abs x)^n / (1 - abs x) :
      begin
        have : abs y ≤ abs x := abs_le.2 hy,
        have : 0 < 1 - abs x, by linarith,
        have : 1 - abs x ≤ abs (1 - y) := le_trans (by linarith [hy.2]) (le_abs_self _),
        simp only [← pow_abs, abs_div, abs_neg],
        apply_rules [div_le_div, pow_nonneg, abs_nonneg, pow_le_pow_of_le_left]
      end },
  -- third step: apply the mean value inequality
  have C : ∥F x - F 0∥ ≤ ((abs x)^n / (1 - abs x)) * ∥x - 0∥,
  { have : ∀ y ∈ Icc (- abs x) (abs x), differentiable_at ℝ F y,
    { assume y hy,
      have : 1 - y ≠ 0 := sub_ne_zero_of_ne (ne_of_gt (lt_of_le_of_lt hy.2 h)),
      simp [F, this] },
    apply convex.norm_image_sub_le_of_norm_deriv_le this B (convex_Icc _ _) _ _,
    { simpa using abs_nonneg x },
    { simp [le_abs_self x, neg_le.mp (neg_le_abs_self x)] } },
  -- fourth step: conclude by massaging the inequality of the third step
  simpa [F, norm_eq_abs, div_mul_eq_mul_div, pow_succ'] using C
end

/-- Power series expansion of the logarithm around `1`. -/
theorem has_sum_pow_div_log_of_abs_lt_1 {x : ℝ} (h : abs x < 1) :
  has_sum (λ (n : ℕ), x ^ (n + 1) / (n + 1)) (-log (1 - x)) :=
begin
  rw summable.has_sum_iff_tendsto_nat,
  show tendsto (λ (n : ℕ), ∑ (i : ℕ) in range n, x ^ (i + 1) / (i + 1)) at_top (𝓝 (-log (1 - x))),
  { rw [tendsto_iff_norm_tendsto_zero],
    simp only [norm_eq_abs, sub_neg_eq_add],
    refine squeeze_zero (λ n, abs_nonneg _) (abs_log_sub_add_sum_range_le h) _,
    suffices : tendsto (λ (t : ℕ), abs x ^ (t + 1) / (1 - abs x)) at_top
      (𝓝 (abs x * 0 / (1 - abs x))), by simpa,
    simp only [pow_succ],
    refine (tendsto_const_nhds.mul _).div_const,
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (abs_nonneg _) h },
  show summable (λ (n : ℕ), x ^ (n + 1) / (n + 1)),
  { refine summable_of_norm_bounded _ (summable_geometric_of_lt_1 (abs_nonneg _) h) (λ i, _),
    calc ∥x ^ (i + 1) / (i + 1)∥
    = abs x ^ (i+1) / (i+1) :
      begin
        have : (0 : ℝ) ≤ i + 1 := le_of_lt (nat.cast_add_one_pos i),
        rw [norm_eq_abs, abs_div, ← pow_abs, abs_of_nonneg this],
      end
    ... ≤ abs x ^ (i+1) / (0 + 1) :
      begin
        apply_rules [div_le_div_of_le_left, pow_nonneg, abs_nonneg, add_le_add_right,
          i.cast_nonneg],
        norm_num,
      end
    ... ≤ abs x ^ i :
      by simpa [pow_succ'] using mul_le_of_le_one_right (pow_nonneg (abs_nonneg x) i) (le_of_lt h) }
end

end real
