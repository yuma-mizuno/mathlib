/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigo_without_deriv
import ring_theory.polynomial.chebyshev
import analysis.special_functions.exp_log

/-!
# Trigonometric functions

## Main definitions

This file contains the following definitions:
* π, arcsin, arccos, arctan
* argument of a complex number
* logarithm on complex numbers

## Main statements

Many basic inequalities on trigonometric functions are established.

The continuity and differentiability of the usual trigonometric functions are proved, and their
derivatives are computed.

* `polynomial.chebyshev.T_complex_cos`: the `n`-th Chebyshev polynomial evaluates on `complex.cos θ`
  to the value `complex.cos (n * θ)`.

## Tags

log, sin, cos, tan, arcsin, arccos, arctan, angle, argument
-/

noncomputable theory
open_locale classical topological_space filter
open set filter

namespace complex

/-- The complex sine function is everywhere strictly differentiable, with the derivative `cos x`. -/
lemma has_strict_deriv_at_sin (x : ℂ) : has_strict_deriv_at sin (cos x) x :=
begin
  simp only [cos, div_eq_mul_inv],
  convert ((((has_strict_deriv_at_id x).neg.mul_const I).cexp.sub
    ((has_strict_deriv_at_id x).mul_const I).cexp).mul_const I).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  rw [sub_mul, mul_assoc, mul_assoc, I_mul_I, neg_one_mul, neg_neg, mul_one, one_mul, mul_assoc,
      I_mul_I, mul_neg_one, sub_neg_eq_add, add_comm]
end

/-- The complex sine function is everywhere differentiable, with the derivative `cos x`. -/
lemma has_deriv_at_sin (x : ℂ) : has_deriv_at sin (cos x) x :=
(has_strict_deriv_at_sin x).has_deriv_at

lemma times_cont_diff_sin {n} : times_cont_diff ℂ n sin :=
(((times_cont_diff_neg.mul times_cont_diff_const).cexp.sub
  (times_cont_diff_id.mul times_cont_diff_const).cexp).mul times_cont_diff_const).div_const

lemma differentiable_sin : differentiable ℂ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin {x : ℂ} : differentiable_at ℂ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

/-- The complex cosine function is everywhere strictly differentiable, with the derivative
`-sin x`. -/
lemma has_strict_deriv_at_cos (x : ℂ) : has_strict_deriv_at cos (-sin x) x :=
begin
  simp only [sin, div_eq_mul_inv, neg_mul_eq_neg_mul],
  convert (((has_strict_deriv_at_id x).mul_const I).cexp.add
    ((has_strict_deriv_at_id x).neg.mul_const I).cexp).mul_const (2:ℂ)⁻¹,
  simp only [function.comp, id],
  ring
end

/-- The complex cosine function is everywhere differentiable, with the derivative `-sin x`. -/
lemma has_deriv_at_cos (x : ℂ) : has_deriv_at cos (-sin x) x :=
(has_strict_deriv_at_cos x).has_deriv_at

lemma times_cont_diff_cos {n} : times_cont_diff ℂ n cos :=
((times_cont_diff_id.mul times_cont_diff_const).cexp.add
  (times_cont_diff_neg.mul times_cont_diff_const).cexp).div_const

lemma differentiable_cos : differentiable ℂ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

lemma deriv_cos {x : ℂ} : deriv cos x = -sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, -sin x) :=
funext $ λ x, deriv_cos

/-- The complex hyperbolic sine function is everywhere strictly differentiable, with the derivative
`cosh x`. -/
lemma has_strict_deriv_at_sinh (x : ℂ) : has_strict_deriv_at sinh (cosh x) x :=
begin
  simp only [cosh, div_eq_mul_inv],
  convert ((has_strict_deriv_at_exp x).sub (has_strict_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg, neg_neg]
end

/-- The complex hyperbolic sine function is everywhere differentiable, with the derivative
`cosh x`. -/
lemma has_deriv_at_sinh (x : ℂ) : has_deriv_at sinh (cosh x) x :=
(has_strict_deriv_at_sinh x).has_deriv_at

lemma times_cont_diff_sinh {n} : times_cont_diff ℂ n sinh :=
(times_cont_diff_exp.sub times_cont_diff_neg.cexp).div_const

lemma differentiable_sinh : differentiable ℂ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh {x : ℂ} : differentiable_at ℂ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

/-- The complex hyperbolic cosine function is everywhere strictly differentiable, with the
derivative `sinh x`. -/
lemma has_strict_deriv_at_cosh (x : ℂ) : has_strict_deriv_at cosh (sinh x) x :=
begin
  simp only [sinh, div_eq_mul_inv],
  convert ((has_strict_deriv_at_exp x).add (has_strict_deriv_at_id x).neg.cexp).mul_const (2:ℂ)⁻¹,
  rw [id, mul_neg_one, sub_eq_add_neg]
end

/-- The complex hyperbolic cosine function is everywhere differentiable, with the derivative
`sinh x`. -/
lemma has_deriv_at_cosh (x : ℂ) : has_deriv_at cosh (sinh x) x :=
(has_strict_deriv_at_cosh x).has_deriv_at

lemma times_cont_diff_cosh {n} : times_cont_diff ℂ n cosh :=
(times_cont_diff_exp.add times_cont_diff_neg.cexp).div_const

lemma differentiable_cosh : differentiable ℂ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh {x : ℂ} : differentiable_at ℂ cos x :=
differentiable_cos x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

end complex

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : ℂ → ℂ` -/

variables {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}

/-! #### `complex.cos` -/

lemma has_strict_deriv_at.ccos (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_strict_deriv_at_cos (f x)).comp x hf

lemma has_deriv_at.ccos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') x :=
(complex.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.ccos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) * f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cos (f x)) s x = - complex.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccos.deriv_within hxs

@[simp] lemma deriv_ccos (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cos (f x)) x = - complex.sin (f x) * (deriv f x) :=
hc.has_deriv_at.ccos.deriv

/-! #### `complex.sin` -/

lemma has_strict_deriv_at.csin (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_strict_deriv_at_sin (f x)).comp x hf

lemma has_deriv_at.csin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') x :=
(complex.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.csin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) * f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sin (f x)) s x = complex.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csin.deriv_within hxs

@[simp] lemma deriv_csin (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sin (f x)) x = complex.cos (f x) * (deriv f x) :=
hc.has_deriv_at.csin.deriv

/-! #### `complex.cosh` -/

lemma has_strict_deriv_at.ccosh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_strict_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_at.ccosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') x :=
(complex.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.ccosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) * f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.cosh (f x)) s x = complex.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.ccosh.deriv_within hxs

@[simp] lemma deriv_ccosh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.cosh (f x)) x = complex.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.ccosh.deriv

/-! #### `complex.sinh` -/

lemma has_strict_deriv_at.csinh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_strict_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_at.csinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') x :=
(complex.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.csinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) * f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  deriv_within (λx, complex.sinh (f x)) s x = complex.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.csinh.deriv_within hxs

@[simp] lemma deriv_csinh (hc : differentiable_at ℂ f x) :
  deriv (λx, complex.sinh (f x)) x = complex.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.csinh.deriv

end

section
/-! ### Simp lemmas for derivatives of `λ x, complex.cos (f x)` etc., `f : E → ℂ` -/

variables {E : Type*} [normed_group E] [normed_space ℂ E] {f : E → ℂ} {f' : E →L[ℂ] ℂ}
  {x : E} {s : set E}

/-! #### `complex.cos` -/

lemma has_strict_fderiv_at.ccos (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') x :=
(complex.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.ccos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cos (f x)) (- complex.sin (f x) • f') s x :=
(complex.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccos (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cos (f x)) s x :=
hf.has_fderiv_within_at.ccos.differentiable_within_at

@[simp] lemma differentiable_at.ccos (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cos (f x)) x :=
hc.has_fderiv_at.ccos.differentiable_at

lemma differentiable_on.ccos (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cos (f x)) s :=
λx h, (hc x h).ccos

@[simp] lemma differentiable.ccos (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cos (f x)) :=
λx, (hc x).ccos

lemma fderiv_within_ccos (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cos (f x)) s x = - complex.sin (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccos.fderiv_within hxs

@[simp] lemma fderiv_ccos (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cos (f x)) x = - complex.sin (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccos.fderiv

lemma times_cont_diff.ccos {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cos (f x)) :=
complex.times_cont_diff_cos.comp h

lemma times_cont_diff_at.ccos {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cos (f x)) x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccos {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cos (f x)) s :=
complex.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccos {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cos (f x)) s x :=
complex.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sin` -/

lemma has_strict_fderiv_at.csin (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') x :=
(complex.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.csin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sin (f x)) (complex.cos (f x) • f') s x :=
(complex.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csin (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sin (f x)) s x :=
hf.has_fderiv_within_at.csin.differentiable_within_at

@[simp] lemma differentiable_at.csin (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sin (f x)) x :=
hc.has_fderiv_at.csin.differentiable_at

lemma differentiable_on.csin (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sin (f x)) s :=
λx h, (hc x h).csin

@[simp] lemma differentiable.csin (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sin (f x)) :=
λx, (hc x).csin

lemma fderiv_within_csin (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sin (f x)) s x = complex.cos (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csin.fderiv_within hxs

@[simp] lemma fderiv_csin (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sin (f x)) x = complex.cos (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csin.fderiv

lemma times_cont_diff.csin {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sin (f x)) :=
complex.times_cont_diff_sin.comp h

lemma times_cont_diff_at.csin {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sin (f x)) x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csin {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sin (f x)) s :=
complex.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csin {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sin (f x)) s x :=
complex.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.cosh` -/

lemma has_strict_fderiv_at.ccosh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') x :=
(complex.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.ccosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.ccosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.cosh (f x)) (complex.sinh (f x) • f') s x :=
(complex.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.ccosh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.cosh (f x)) s x :=
hf.has_fderiv_within_at.ccosh.differentiable_within_at

@[simp] lemma differentiable_at.ccosh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.cosh (f x)) x :=
hc.has_fderiv_at.ccosh.differentiable_at

lemma differentiable_on.ccosh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.cosh (f x)) s :=
λx h, (hc x h).ccosh

@[simp] lemma differentiable.ccosh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.cosh (f x)) :=
λx, (hc x).ccosh

lemma fderiv_within_ccosh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.cosh (f x)) s x = complex.sinh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.ccosh.fderiv_within hxs

@[simp] lemma fderiv_ccosh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.cosh (f x)) x = complex.sinh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.ccosh.fderiv

lemma times_cont_diff.ccosh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.cosh (f x)) :=
complex.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.ccosh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.cosh (f x)) x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.ccosh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.cosh (f x)) s :=
complex.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.ccosh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.cosh (f x)) s x :=
complex.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `complex.sinh` -/

lemma has_strict_fderiv_at.csinh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') x :=
(complex.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.csinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.csinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, complex.sinh (f x)) (complex.cosh (f x) • f') s x :=
(complex.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.csinh (hf : differentiable_within_at ℂ f s x) :
  differentiable_within_at ℂ (λ x, complex.sinh (f x)) s x :=
hf.has_fderiv_within_at.csinh.differentiable_within_at

@[simp] lemma differentiable_at.csinh (hc : differentiable_at ℂ f x) :
  differentiable_at ℂ (λx, complex.sinh (f x)) x :=
hc.has_fderiv_at.csinh.differentiable_at

lemma differentiable_on.csinh (hc : differentiable_on ℂ f s) :
  differentiable_on ℂ (λx, complex.sinh (f x)) s :=
λx h, (hc x h).csinh

@[simp] lemma differentiable.csinh (hc : differentiable ℂ f) :
  differentiable ℂ (λx, complex.sinh (f x)) :=
λx, (hc x).csinh

lemma fderiv_within_csinh (hf : differentiable_within_at ℂ f s x)
  (hxs : unique_diff_within_at ℂ s x) :
  fderiv_within ℂ (λx, complex.sinh (f x)) s x = complex.cosh (f x) • (fderiv_within ℂ f s x) :=
hf.has_fderiv_within_at.csinh.fderiv_within hxs

@[simp] lemma fderiv_csinh (hc : differentiable_at ℂ f x) :
  fderiv ℂ (λx, complex.sinh (f x)) x = complex.cosh (f x) • (fderiv ℂ f x) :=
hc.has_fderiv_at.csinh.fderiv

lemma times_cont_diff.csinh {n} (h : times_cont_diff ℂ n f) :
  times_cont_diff ℂ n (λ x, complex.sinh (f x)) :=
complex.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.csinh {n} (hf : times_cont_diff_at ℂ n f x) :
  times_cont_diff_at ℂ n (λ x, complex.sinh (f x)) x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.csinh {n} (hf : times_cont_diff_on ℂ n f s) :
  times_cont_diff_on ℂ n (λ x, complex.sinh (f x)) s :=
complex.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.csinh {n} (hf : times_cont_diff_within_at ℂ n f s x) :
  times_cont_diff_within_at ℂ n (λ x, complex.sinh (f x)) s x :=
complex.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real

variables {x y z : ℝ}

lemma has_strict_deriv_at_sin (x : ℝ) : has_strict_deriv_at sin (cos x) x :=
(complex.has_strict_deriv_at_sin x).real_of_complex

lemma has_deriv_at_sin (x : ℝ) : has_deriv_at sin (cos x) x :=
(has_strict_deriv_at_sin x).has_deriv_at

lemma times_cont_diff_sin {n} : times_cont_diff ℝ n sin :=
complex.times_cont_diff_sin.real_of_complex

lemma differentiable_sin : differentiable ℝ sin :=
λx, (has_deriv_at_sin x).differentiable_at

lemma differentiable_at_sin : differentiable_at ℝ sin x :=
differentiable_sin x

@[simp] lemma deriv_sin : deriv sin = cos :=
funext $ λ x, (has_deriv_at_sin x).deriv

lemma has_strict_deriv_at_cos (x : ℝ) : has_strict_deriv_at cos (-sin x) x :=
(complex.has_strict_deriv_at_cos x).real_of_complex

lemma has_deriv_at_cos (x : ℝ) : has_deriv_at cos (-sin x) x :=
(complex.has_deriv_at_cos x).real_of_complex

lemma times_cont_diff_cos {n} : times_cont_diff ℝ n cos :=
complex.times_cont_diff_cos.real_of_complex

lemma differentiable_cos : differentiable ℝ cos :=
λx, (has_deriv_at_cos x).differentiable_at

lemma differentiable_at_cos : differentiable_at ℝ cos x :=
differentiable_cos x

lemma deriv_cos : deriv cos x = - sin x :=
(has_deriv_at_cos x).deriv

@[simp] lemma deriv_cos' : deriv cos = (λ x, - sin x) :=
funext $ λ _, deriv_cos

lemma has_strict_deriv_at_sinh (x : ℝ) : has_strict_deriv_at sinh (cosh x) x :=
(complex.has_strict_deriv_at_sinh x).real_of_complex

lemma has_deriv_at_sinh (x : ℝ) : has_deriv_at sinh (cosh x) x :=
(complex.has_deriv_at_sinh x).real_of_complex

lemma times_cont_diff_sinh {n} : times_cont_diff ℝ n sinh :=
complex.times_cont_diff_sinh.real_of_complex

lemma differentiable_sinh : differentiable ℝ sinh :=
λx, (has_deriv_at_sinh x).differentiable_at

lemma differentiable_at_sinh : differentiable_at ℝ sinh x :=
differentiable_sinh x

@[simp] lemma deriv_sinh : deriv sinh = cosh :=
funext $ λ x, (has_deriv_at_sinh x).deriv

lemma has_strict_deriv_at_cosh (x : ℝ) : has_strict_deriv_at cosh (sinh x) x :=
(complex.has_strict_deriv_at_cosh x).real_of_complex

lemma has_deriv_at_cosh (x : ℝ) : has_deriv_at cosh (sinh x) x :=
(complex.has_deriv_at_cosh x).real_of_complex

lemma times_cont_diff_cosh {n} : times_cont_diff ℝ n cosh :=
complex.times_cont_diff_cosh.real_of_complex

lemma differentiable_cosh : differentiable ℝ cosh :=
λx, (has_deriv_at_cosh x).differentiable_at

lemma differentiable_at_cosh : differentiable_at ℝ cosh x :=
differentiable_cosh x

@[simp] lemma deriv_cosh : deriv cosh = sinh :=
funext $ λ x, (has_deriv_at_cosh x).deriv

/-- `sinh` is strictly monotone. -/
lemma sinh_strict_mono : strict_mono sinh :=
strict_mono_of_deriv_pos differentiable_sinh (by { rw [real.deriv_sinh], exact cosh_pos })

end real

section
/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : ℝ → ℝ` -/

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

/-! #### `real.cos` -/

lemma has_strict_deriv_at.cos (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_strict_deriv_at_cos (f x)).comp x hf

lemma has_deriv_at.cos (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cos (f x)) (- real.sin (f x) * f') x :=
(real.has_deriv_at_cos (f x)).comp x hf

lemma has_deriv_within_at.cos (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cos (f x)) (- real.sin (f x) * f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cos (f x)) s x = - real.sin (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cos.deriv_within hxs

@[simp] lemma deriv_cos (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cos (f x)) x = - real.sin (f x) * (deriv f x) :=
hc.has_deriv_at.cos.deriv

/-! #### `real.sin` -/

lemma has_strict_deriv_at.sin (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_strict_deriv_at_sin (f x)).comp x hf

lemma has_deriv_at.sin (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sin (f x)) (real.cos (f x) * f') x :=
(real.has_deriv_at_sin (f x)).comp x hf

lemma has_deriv_within_at.sin (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sin (f x)) (real.cos (f x) * f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sin (f x)) s x = real.cos (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sin.deriv_within hxs

@[simp] lemma deriv_sin (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sin (f x)) x = real.cos (f x) * (deriv f x) :=
hc.has_deriv_at.sin.deriv

/-! #### `real.cosh` -/

lemma has_strict_deriv_at.cosh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_strict_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_at.cosh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') x :=
(real.has_deriv_at_cosh (f x)).comp x hf

lemma has_deriv_within_at.cosh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) * f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.cosh (f x)) s x = real.sinh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.cosh.deriv_within hxs

@[simp] lemma deriv_cosh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.cosh (f x)) x = real.sinh (f x) * (deriv f x) :=
hc.has_deriv_at.cosh.deriv

/-! #### `real.sinh` -/

lemma has_strict_deriv_at.sinh (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_strict_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_at.sinh (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') x :=
(real.has_deriv_at_sinh (f x)).comp x hf

lemma has_deriv_within_at.sinh (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) * f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λx, real.sinh (f x)) s x = real.cosh (f x) * (deriv_within f s x) :=
hf.has_deriv_within_at.sinh.deriv_within hxs

@[simp] lemma deriv_sinh (hc : differentiable_at ℝ f x) :
  deriv (λx, real.sinh (f x)) x = real.cosh (f x) * (deriv f x) :=
hc.has_deriv_at.sinh.deriv

end

section

/-! ### Simp lemmas for derivatives of `λ x, real.cos (f x)` etc., `f : E → ℝ` -/

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ}
  {x : E} {s : set E}

/-! #### `real.cos` -/

lemma has_strict_fderiv_at.cos (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.cos (f x)) (- real.sin (f x) • f') x :=
(real.has_strict_deriv_at_cos (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.cos (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cos (f x)) (- real.sin (f x) • f') x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cos (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cos (f x)) (- real.sin (f x) • f') s x :=
(real.has_deriv_at_cos (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cos (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cos (f x)) s x :=
hf.has_fderiv_within_at.cos.differentiable_within_at

@[simp] lemma differentiable_at.cos (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cos (f x)) x :=
hc.has_fderiv_at.cos.differentiable_at

lemma differentiable_on.cos (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cos (f x)) s :=
λx h, (hc x h).cos

@[simp] lemma differentiable.cos (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cos (f x)) :=
λx, (hc x).cos

lemma fderiv_within_cos (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cos (f x)) s x = - real.sin (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cos.fderiv_within hxs

@[simp] lemma fderiv_cos (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cos (f x)) x = - real.sin (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cos.fderiv

lemma times_cont_diff.cos {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cos (f x)) :=
real.times_cont_diff_cos.comp h

lemma times_cont_diff_at.cos {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cos (f x)) x :=
real.times_cont_diff_cos.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cos {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cos (f x)) s :=
real.times_cont_diff_cos.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cos {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cos (f x)) s x :=
real.times_cont_diff_cos.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sin` -/

lemma has_strict_fderiv_at.sin (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.sin (f x)) (real.cos (f x) • f') x :=
(real.has_strict_deriv_at_sin (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.sin (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sin (f x)) (real.cos (f x) • f') x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sin (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sin (f x)) (real.cos (f x) • f') s x :=
(real.has_deriv_at_sin (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sin (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sin (f x)) s x :=
hf.has_fderiv_within_at.sin.differentiable_within_at

@[simp] lemma differentiable_at.sin (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sin (f x)) x :=
hc.has_fderiv_at.sin.differentiable_at

lemma differentiable_on.sin (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sin (f x)) s :=
λx h, (hc x h).sin

@[simp] lemma differentiable.sin (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sin (f x)) :=
λx, (hc x).sin

lemma fderiv_within_sin (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sin (f x)) s x = real.cos (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sin.fderiv_within hxs

@[simp] lemma fderiv_sin (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sin (f x)) x = real.cos (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sin.fderiv

lemma times_cont_diff.sin {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sin (f x)) :=
real.times_cont_diff_sin.comp h

lemma times_cont_diff_at.sin {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sin (f x)) x :=
real.times_cont_diff_sin.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sin {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sin (f x)) s :=
real.times_cont_diff_sin.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sin {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sin (f x)) s x :=
real.times_cont_diff_sin.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.cosh` -/

lemma has_strict_fderiv_at.cosh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') x :=
(real.has_strict_deriv_at_cosh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.cosh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.cosh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.cosh (f x)) (real.sinh (f x) • f') s x :=
(real.has_deriv_at_cosh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.cosh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.cosh (f x)) s x :=
hf.has_fderiv_within_at.cosh.differentiable_within_at

@[simp] lemma differentiable_at.cosh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.cosh (f x)) x :=
hc.has_fderiv_at.cosh.differentiable_at

lemma differentiable_on.cosh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.cosh (f x)) s :=
λx h, (hc x h).cosh

@[simp] lemma differentiable.cosh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.cosh (f x)) :=
λx, (hc x).cosh

lemma fderiv_within_cosh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.cosh (f x)) s x = real.sinh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.cosh.fderiv_within hxs

@[simp] lemma fderiv_cosh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.cosh (f x)) x = real.sinh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.cosh.fderiv

lemma times_cont_diff.cosh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.cosh (f x)) :=
real.times_cont_diff_cosh.comp h

lemma times_cont_diff_at.cosh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.cosh (f x)) x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.cosh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.cosh (f x)) s :=
real.times_cont_diff_cosh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.cosh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.cosh (f x)) s x :=
real.times_cont_diff_cosh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

/-! #### `real.sinh` -/

lemma has_strict_fderiv_at.sinh (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') x :=
(real.has_strict_deriv_at_sinh (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.sinh (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.sinh (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, real.sinh (f x)) (real.cosh (f x) • f') s x :=
(real.has_deriv_at_sinh (f x)).comp_has_fderiv_within_at x hf

lemma differentiable_within_at.sinh (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.sinh (f x)) s x :=
hf.has_fderiv_within_at.sinh.differentiable_within_at

@[simp] lemma differentiable_at.sinh (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λx, real.sinh (f x)) x :=
hc.has_fderiv_at.sinh.differentiable_at

lemma differentiable_on.sinh (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λx, real.sinh (f x)) s :=
λx h, (hc x h).sinh

@[simp] lemma differentiable.sinh (hc : differentiable ℝ f) :
  differentiable ℝ (λx, real.sinh (f x)) :=
λx, (hc x).sinh

lemma fderiv_within_sinh (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λx, real.sinh (f x)) s x = real.cosh (f x) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.sinh.fderiv_within hxs

@[simp] lemma fderiv_sinh (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λx, real.sinh (f x)) x = real.cosh (f x) • (fderiv ℝ f x) :=
hc.has_fderiv_at.sinh.fderiv

lemma times_cont_diff.sinh {n} (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, real.sinh (f x)) :=
real.times_cont_diff_sinh.comp h

lemma times_cont_diff_at.sinh {n} (hf : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, real.sinh (f x)) x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp x hf

lemma times_cont_diff_on.sinh {n} (hf : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, real.sinh (f x)) s :=
real.times_cont_diff_sinh.comp_times_cont_diff_on  hf

lemma times_cont_diff_within_at.sinh {n} (hf : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, real.sinh (f x)) s x :=
real.times_cont_diff_sinh.times_cont_diff_at.comp_times_cont_diff_within_at x hf

end

namespace real
open_locale real

lemma deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x ∧ times_cont_diff_at ℝ ⊤ arcsin x :=
begin
  cases h₁.lt_or_lt with h₁ h₁,
  { have : 1 - x ^ 2 < 0, by nlinarith [h₁],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, -(π / 2) :=
      (gt_mem_nhds h₁).mono (λ y hy, arcsin_of_le_neg_one hy.le),
    exact ⟨(has_strict_deriv_at_const _ _).congr_of_eventually_eq this.symm,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ },
  cases h₂.lt_or_lt with h₂ h₂,
  { have : 0 < sqrt (1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂]),
    simp only [← cos_arcsin h₁.le h₂.le, one_div] at this ⊢,
    exact ⟨sin_local_homeomorph.has_strict_deriv_at_symm ⟨h₁, h₂⟩ this.ne'
      (has_strict_deriv_at_sin _),
      sin_local_homeomorph.times_cont_diff_at_symm_deriv this.ne' ⟨h₁, h₂⟩
        (has_deriv_at_sin _) times_cont_diff_sin.times_cont_diff_at⟩ },
  { have : 1 - x ^ 2 < 0, by nlinarith [h₂],
    rw [sqrt_eq_zero'.2 this.le, div_zero],
    have : arcsin =ᶠ[𝓝 x] λ _, π / 2 := (lt_mem_nhds h₂).mono (λ y hy, arcsin_of_one_le hy.le),
    exact ⟨(has_strict_deriv_at_const _ _).congr_of_eventually_eq this.symm,
      times_cont_diff_at_const.congr_of_eventually_eq this⟩ }
end

lemma has_strict_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x :=
(deriv_arcsin_aux h₁ h₂).1

lemma has_deriv_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arcsin (1 / sqrt (1 - x ^ 2)) x :=
(has_strict_deriv_at_arcsin h₁ h₂).has_deriv_at

lemma times_cont_diff_at_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x :=
(deriv_arcsin_aux h₁ h₂).2.of_le le_top

lemma has_deriv_within_at_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Ici x) x :=
begin
  rcases em (x = 1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (π / 2)).congr _ _;
      simp [arcsin_of_one_le] { contextual := tt } },
  { exact (has_deriv_at_arcsin h h').has_deriv_within_at }
end

lemma has_deriv_within_at_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arcsin (1 / sqrt (1 - x ^ 2)) (Iic x) x :=
begin
  rcases em (x = -1) with (rfl|h'),
  { convert (has_deriv_within_at_const _ _ (-(π / 2))).congr _ _;
      simp [arcsin_of_le_neg_one] { contextual := tt } },
  { exact (has_deriv_at_arcsin h' h).has_deriv_within_at }
end

lemma differentiable_within_at_arcsin_Ici {x : ℝ} :
  differentiable_within_at ℝ arcsin (Ici x) x ↔ x ≠ -1 :=
begin
  refine ⟨_, λ h, (has_deriv_within_at_arcsin_Ici h).differentiable_within_at⟩,
  rintro h rfl,
  have : sin ∘ arcsin =ᶠ[𝓝[Ici (-1:ℝ)] (-1)] id,
  { filter_upwards [Icc_mem_nhds_within_Ici ⟨le_rfl, neg_lt_self (@zero_lt_one ℝ _ _)⟩],
    exact λ x, sin_arcsin' },
  have := h.has_deriv_within_at.sin.congr_of_eventually_eq this.symm (by simp),
  simpa using (unique_diff_on_Ici _ _ left_mem_Ici).eq_deriv _ this (has_deriv_within_at_id _ _)
end

lemma differentiable_within_at_arcsin_Iic {x : ℝ} :
  differentiable_within_at ℝ arcsin (Iic x) x ↔ x ≠ 1 :=
begin
  refine ⟨λ h, _, λ h, (has_deriv_within_at_arcsin_Iic h).differentiable_within_at⟩,
  rw [← neg_neg x, ← image_neg_Ici] at h,
  have := (h.comp (-x) differentiable_within_at_id.neg (maps_to_image _ _)).neg,
  simpa [(∘), differentiable_within_at_arcsin_Ici] using this
end

lemma differentiable_at_arcsin {x : ℝ} :
  differentiable_at ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
⟨λ h, ⟨differentiable_within_at_arcsin_Ici.1 h.differentiable_within_at,
  differentiable_within_at_arcsin_Iic.1 h.differentiable_within_at⟩,
  λ h, (has_deriv_at_arcsin h.1 h.2).differentiable_at⟩

@[simp] lemma deriv_arcsin : deriv arcsin = λ x, 1 / sqrt (1 - x ^ 2) :=
begin
  funext x,
  by_cases h : x ≠ -1 ∧ x ≠ 1,
  { exact (has_deriv_at_arcsin h.1 h.2).deriv },
  { rw [deriv_zero_of_not_differentiable_at (mt differentiable_at_arcsin.1 h)],
    simp only [not_and_distrib, ne.def, not_not] at h,
    rcases h with (rfl|rfl); simp }
end

lemma differentiable_on_arcsin : differentiable_on ℝ arcsin {-1, 1}ᶜ :=
λ x hx, (differentiable_at_arcsin.2
  ⟨λ h, hx (or.inl h), λ h, hx (or.inr h)⟩).differentiable_within_at

lemma times_cont_diff_on_arcsin {n : with_top ℕ} :
  times_cont_diff_on ℝ n arcsin {-1, 1}ᶜ :=
λ x hx, (times_cont_diff_at_arcsin (mt or.inl hx) (mt or.inr hx)).times_cont_diff_within_at

lemma times_cont_diff_at_arcsin_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arcsin x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
⟨λ h, or_iff_not_imp_left.2 $ λ hn, differentiable_at_arcsin.1 $ h.differentiable_at $
  with_top.one_le_iff_pos.2 (pos_iff_ne_zero.2 hn),
  λ h, h.elim (λ hn, hn.symm ▸ (times_cont_diff_zero.2 continuous_arcsin).times_cont_diff_at) $
    λ hx, times_cont_diff_at_arcsin hx.1 hx.2⟩

lemma has_strict_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_strict_deriv_at arccos (-(1 / sqrt (1 - x ^ 2))) x :=
(has_strict_deriv_at_arcsin h₁ h₂).const_sub (π / 2)

lemma has_deriv_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
  has_deriv_at arccos (-(1 / sqrt (1 - x ^ 2))) x :=
(has_deriv_at_arcsin h₁ h₂).const_sub (π / 2)

lemma times_cont_diff_at_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x :=
times_cont_diff_at_const.sub (times_cont_diff_at_arcsin h₁ h₂)

lemma has_deriv_within_at_arccos_Ici {x : ℝ} (h : x ≠ -1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Ici x) x :=
(has_deriv_within_at_arcsin_Ici h).const_sub _

lemma has_deriv_within_at_arccos_Iic {x : ℝ} (h : x ≠ 1) :
  has_deriv_within_at arccos (-(1 / sqrt (1 - x ^ 2))) (Iic x) x :=
(has_deriv_within_at_arcsin_Iic h).const_sub _

lemma differentiable_within_at_arccos_Ici {x : ℝ} :
  differentiable_within_at ℝ arccos (Ici x) x ↔ x ≠ -1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Ici

lemma differentiable_within_at_arccos_Iic {x : ℝ} :
  differentiable_within_at ℝ arccos (Iic x) x ↔ x ≠ 1 :=
(differentiable_within_at_const_sub_iff _).trans differentiable_within_at_arcsin_Iic

lemma differentiable_at_arccos {x : ℝ} :
  differentiable_at ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
(differentiable_at_const_sub_iff _).trans differentiable_at_arcsin

@[simp] lemma deriv_arccos : deriv arccos = λ x, -(1 / sqrt (1 - x ^ 2)) :=
funext $ λ x, (deriv_const_sub _).trans $ by simp only [deriv_arcsin]

lemma differentiable_on_arccos : differentiable_on ℝ arccos {-1, 1}ᶜ :=
differentiable_on_arcsin.const_sub _

lemma times_cont_diff_on_arccos {n : with_top ℕ} :
  times_cont_diff_on ℝ n arccos {-1, 1}ᶜ :=
times_cont_diff_on_const.sub times_cont_diff_on_arcsin

lemma times_cont_diff_at_arccos_iff {x : ℝ} {n : with_top ℕ} :
  times_cont_diff_at ℝ n arccos x ↔ n = 0 ∨ (x ≠ -1 ∧ x ≠ 1) :=
by refine iff.trans ⟨λ h, _, λ h, _⟩ times_cont_diff_at_arcsin_iff;
  simpa [arccos] using (@times_cont_diff_at_const _ _ _ _ _ _ _ _ _ _ (π / 2)).sub h

end real

namespace complex

open_locale real

/-- `complex.exp` as a `local_homeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}`. This definition is used to prove that `complex.log`
is complex differentiable at all points but the negative real semi-axis. -/
def exp_local_homeomorph : local_homeomorph ℂ ℂ :=
local_homeomorph.of_continuous_open
{ to_fun := exp,
  inv_fun := log,
  source := {z : ℂ | z.im ∈ Ioo (- π) π},
  target := {z : ℂ | 0 < z.re} ∪ {z : ℂ | z.im ≠ 0},
  map_source' :=
    begin
      rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩,
      refine (not_or_of_imp $ λ hz, _).symm,
      obtain rfl : y = 0,
      { rw exp_im at hz,
        simpa [(real.exp_pos _).ne', real.sin_eq_zero_iff_of_lt_of_lt h₁ h₂] using hz },
      rw [mem_set_of_eq, ← of_real_def, exp_of_real_re],
      exact real.exp_pos x
    end,
  map_target' := λ z h,
    suffices 0 ≤ z.re ∨ z.im ≠ 0,
      by simpa [log_im, neg_pi_lt_arg, (arg_le_pi _).lt_iff_ne, arg_eq_pi_iff, not_and_distrib],
    h.imp (λ h, le_of_lt h) id,
  left_inv' := λ x hx, log_exp hx.1 (le_of_lt hx.2),
  right_inv' := λ x hx, exp_log $ by { rintro rfl, simpa [lt_irrefl] using hx } }
continuous_exp.continuous_on is_open_map_exp (is_open_Ioo.preimage continuous_im)

lemma has_strict_deriv_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
  has_strict_deriv_at log x⁻¹ x :=
have h0 :  x ≠ 0, by { rintro rfl, simpa [lt_irrefl] using h },
exp_local_homeomorph.has_strict_deriv_at_symm h h0 $
  by simpa [exp_log h0] using has_strict_deriv_at_exp (log x)

lemma times_cont_diff_at_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) {n : with_top ℕ} :
  times_cont_diff_at ℂ n log x :=
exp_local_homeomorph.times_cont_diff_at_symm_deriv (exp_ne_zero $ log x) h
  (has_deriv_at_exp _) times_cont_diff_exp.times_cont_diff_at

lemma has_strict_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) :
  has_strict_deriv_at tan (1 / (cos x)^2) x :=
begin
  convert (has_strict_deriv_at_sin x).div (has_strict_deriv_at_cos x) h,
  rw ← sin_sq_add_cos_sq x,
  ring,
end

lemma has_deriv_at_tan {x : ℂ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
(has_strict_deriv_at_tan h).has_deriv_at

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℂ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
begin
  simp only [tan_eq_sin_div_cos, ← norm_eq_abs, normed_field.norm_div],
  have A : sin x ≠ 0 := λ h, by simpa [*, sq] using sin_sq_add_cos_sq x,
  have B : tendsto cos (𝓝[{x}ᶜ] (x)) (𝓝[{0}ᶜ] 0),
  { refine tendsto_inf.2 ⟨tendsto.mono_left _ inf_le_left, tendsto_principal.2 _⟩,
    exacts [continuous_cos.tendsto' x 0 hx,
      hx ▸ (has_deriv_at_cos _).eventually_ne (neg_ne_zero.2 A)] },
  exact continuous_sin.continuous_within_at.norm.mul_at_top (norm_pos_iff.2 A)
    (tendsto_norm_nhds_within_zero.comp B).inv_tendsto_zero,
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[{(2 * k + 1) * π / 2}ᶜ] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

@[simp] lemma continuous_at_tan {x : ℂ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

@[simp] lemma differentiable_at_tan {x : ℂ} : differentiable_at ℂ tan x ↔ cos x ≠ 0:=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℂ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℂ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, sq]
else (has_deriv_at_tan h).deriv

@[simp] lemma times_cont_diff_at_tan {x : ℂ} {n : with_top ℕ} :
  times_cont_diff_at ℂ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  times_cont_diff_sin.times_cont_diff_at.div times_cont_diff_cos.times_cont_diff_at⟩

end complex

section log_deriv

open complex

variables {α : Type*}

variables [topological_space α]

variables {E : Type*} [normed_group E] [normed_space ℂ E]

lemma has_strict_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_strict_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).comp_has_strict_fderiv_at x h₁

lemma has_strict_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_strict_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_strict_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).comp x h₁ }

lemma has_fderiv_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
  (h₁ : has_fderiv_at f f' x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_at (λ t, log (f t)) ((f x)⁻¹ • f') x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_at x h₁

lemma has_deriv_at.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : has_deriv_at f f' x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_at (λ t, log (f t)) (f' / f x) x :=
by { rw div_eq_inv_mul, exact (has_strict_deriv_at_log h₂).has_deriv_at.comp x h₁ }

lemma differentiable_at.clog {f : E → ℂ} {x : E} (h₁ : differentiable_at ℂ f x)
  (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_at ℂ (λ t, log (f t)) x :=
(h₁.has_fderiv_at.clog h₂).differentiable_at

lemma has_fderiv_within_at.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {s : set E} {x : E}
  (h₁ : has_fderiv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_fderiv_within_at (λ t, log (f t)) ((f x)⁻¹ • f') s x :=
(has_strict_deriv_at_log h₂).has_deriv_at.comp_has_fderiv_within_at x h₁

lemma has_deriv_within_at.clog {f : ℂ → ℂ} {f' x : ℂ} {s : set ℂ}
  (h₁ : has_deriv_within_at f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  has_deriv_within_at (λ t, log (f t)) (f' / f x) s x :=
by { rw div_eq_inv_mul,
     exact (has_strict_deriv_at_log h₂).has_deriv_at.comp_has_deriv_within_at x h₁ }

lemma differentiable_within_at.clog {f : E → ℂ} {s : set E} {x : E}
  (h₁ : differentiable_within_at ℂ f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_within_at ℂ (λ t, log (f t)) s x :=
(h₁.has_fderiv_within_at.clog h₂).differentiable_within_at

lemma differentiable_on.clog {f : E → ℂ} {s : set E}
  (h₁ : differentiable_on ℂ f s) (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable_on ℂ (λ t, log (f t)) s :=
λ x hx, (h₁ x hx).clog (h₂ x hx)

lemma differentiable.clog {f : E → ℂ} (h₁ : differentiable ℂ f)
  (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) :
  differentiable ℂ (λ t, log (f t)) :=
λ x, (h₁ x).clog (h₂ x)

end log_deriv

namespace polynomial.chebyshev

open polynomial complex

/-- The `n`-th Chebyshev polynomial of the first kind evaluates on `cos θ` to the
value `cos (n * θ)`. -/
lemma T_complex_cos (θ : ℂ) :
  ∀ n, (T ℂ n).eval (cos θ) = cos (n * θ)
| 0       := by simp only [T_zero, eval_one, nat.cast_zero, zero_mul, cos_zero]
| 1       := by simp only [eval_X, one_mul, T_one, nat.cast_one]
| (n + 2) :=
begin
  simp only [eval_X, eval_one, T_add_two, eval_sub, eval_bit0, nat.cast_succ, eval_mul],
  rw [T_complex_cos (n + 1), T_complex_cos n],
  have aux : sin θ * sin θ = 1 - cos θ * cos θ,
  { rw ← sin_sq_add_cos_sq θ, ring, },
  simp only [nat.cast_add, nat.cast_one, add_mul, cos_add, one_mul, sin_add, mul_assoc, aux],
  ring,
end

/-- `cos (n * θ)` is equal to the `n`-th Chebyshev polynomial of the first kind evaluated
on `cos θ`. -/
lemma cos_nat_mul (n : ℕ) (θ : ℂ) :
  cos (n * θ) = (T ℂ n).eval (cos θ) :=
(T_complex_cos θ n).symm

/-- The `n`-th Chebyshev polynomial of the second kind evaluates on `cos θ` to the
value `sin ((n+1) * θ) / sin θ`. -/
lemma U_complex_cos (θ : ℂ) (n : ℕ) :
  (U ℂ n).eval (cos θ) * sin θ = sin ((n+1) * θ) :=
begin
  induction n with d hd,
  { simp only [U_zero, nat.cast_zero, eval_one, mul_one, zero_add, one_mul] },
  { rw U_eq_X_mul_U_add_T,
    simp only [eval_add, eval_mul, eval_X, T_complex_cos, add_mul, mul_assoc, hd, one_mul],
    conv_rhs { rw [sin_add, mul_comm] },
    push_cast,
    simp only [add_mul, one_mul] }
end

/-- `sin ((n + 1) * θ)` is equal to `sin θ` multiplied with the `n`-th Chebyshev polynomial of the
second kind evaluated on `cos θ`. -/
lemma sin_nat_succ_mul (n : ℕ) (θ : ℂ) :
  sin ((n + 1) * θ) = (U ℂ n).eval (cos θ) * sin θ :=
(U_complex_cos θ n).symm

end polynomial.chebyshev

namespace real
open_locale real

lemma has_strict_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_strict_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_strict_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma has_deriv_at_tan {x : ℝ} (h : cos x ≠ 0) :
  has_deriv_at tan (1 / (cos x)^2) x :=
by exact_mod_cast (complex.has_deriv_at_tan (by exact_mod_cast h)).real_of_complex

lemma tendsto_abs_tan_of_cos_eq_zero {x : ℝ} (hx : cos x = 0) :
  tendsto (λ x, abs (tan x)) (𝓝[{x}ᶜ] x) at_top :=
begin
  have hx : complex.cos x = 0, by exact_mod_cast hx,
  simp only [← complex.abs_of_real, complex.of_real_tan],
  refine (complex.tendsto_abs_tan_of_cos_eq_zero hx).comp _,
  refine tendsto.inf complex.continuous_of_real.continuous_at _,
  exact tendsto_principal_principal.2 (λ y, mt complex.of_real_inj.1)
end

lemma tendsto_abs_tan_at_top (k : ℤ) :
  tendsto (λ x, abs (tan x)) (𝓝[{(2 * k + 1) * π / 2}ᶜ] ((2 * k + 1) * π / 2)) at_top :=
tendsto_abs_tan_of_cos_eq_zero $ cos_eq_zero_iff.2 ⟨k, rfl⟩

lemma continuous_at_tan {x : ℝ} : continuous_at tan x ↔ cos x ≠ 0 :=
begin
  refine ⟨λ hc h₀, _, λ h, (has_deriv_at_tan h).continuous_at⟩,
  exact not_tendsto_nhds_of_tendsto_at_top (tendsto_abs_tan_of_cos_eq_zero h₀) _
    (hc.norm.tendsto.mono_left inf_le_left)
end

lemma differentiable_at_tan {x : ℝ} : differentiable_at ℝ tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at, λ h, (has_deriv_at_tan h).differentiable_at⟩

@[simp] lemma deriv_tan (x : ℝ) : deriv tan x = 1 / (cos x)^2 :=
if h : cos x = 0 then
  have ¬differentiable_at ℝ tan x := mt differentiable_at_tan.1 (not_not.2 h),
  by simp [deriv_zero_of_not_differentiable_at this, h, sq]
else (has_deriv_at_tan h).deriv

@[simp] lemma times_cont_diff_at_tan {n x} : times_cont_diff_at ℝ n tan x ↔ cos x ≠ 0 :=
⟨λ h, continuous_at_tan.1 h.continuous_at,
  λ h, (complex.times_cont_diff_at_tan.2 $ by exact_mod_cast h).real_of_complex⟩

lemma continuous_on_tan : continuous_on tan {x | cos x ≠ 0} :=
λ x hx, (continuous_at_tan.2 hx).continuous_within_at

@[continuity]
lemma continuous_tan : continuous (λ x : {x | cos x ≠ 0}, tan x) :=
continuous_on_iff_continuous_restrict.1 continuous_on_tan

lemma has_deriv_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  has_deriv_at tan (1 / (cos x)^2) x :=
has_deriv_at_tan (cos_pos_of_mem_Ioo h).ne'

lemma differentiable_at_tan_of_mem_Ioo {x : ℝ} (h : x ∈ Ioo (-(π/2):ℝ) (π/2)) :
  differentiable_at ℝ tan x :=
(has_deriv_at_tan_of_mem_Ioo h).differentiable_at

lemma continuous_on_tan_Ioo : continuous_on tan (Ioo (-(π/2)) (π/2)) :=
λ x hx, (differentiable_at_tan_of_mem_Ioo hx).continuous_at.continuous_within_at

lemma tendsto_sin_pi_div_two : tendsto sin (𝓝[Iio (π/2)] (π/2)) (𝓝 1) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_pi_div_two : tendsto cos (𝓝[Iio (π/2)] (π/2)) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Iio (right_mem_Ioc.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_pi_div_two : tendsto tan (𝓝[Iio (π/2)] (π/2)) at_top :=
begin
  convert tendsto_cos_pi_div_two.inv_tendsto_zero.at_top_mul zero_lt_one
            tendsto_sin_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma tendsto_sin_neg_pi_div_two : tendsto sin (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝 (-1)) :=
by { convert continuous_sin.continuous_within_at, simp }

lemma tendsto_cos_neg_pi_div_two : tendsto cos (𝓝[Ioi (-(π/2))] (-(π/2))) (𝓝[Ioi 0] 0) :=
begin
  apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
  { convert continuous_cos.continuous_within_at, simp },
  { filter_upwards [Ioo_mem_nhds_within_Ioi (left_mem_Ico.mpr (norm_num.lt_neg_pos
      _ _ pi_div_two_pos pi_div_two_pos))] λ x hx, cos_pos_of_mem_Ioo hx },
end

lemma tendsto_tan_neg_pi_div_two : tendsto tan (𝓝[Ioi (-(π/2))] (-(π/2))) at_bot :=
begin
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_zero.at_top_mul_neg (by norm_num)
            tendsto_sin_neg_pi_div_two,
  simp only [pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
end

lemma surj_on_tan : surj_on tan (Ioo (-(π / 2)) (π / 2)) univ :=
have _ := neg_lt_self pi_div_two_pos,
continuous_on_tan_Ioo.surj_on_of_tendsto (nonempty_Ioo.2 this)
  (by simp [tendsto_tan_neg_pi_div_two, this]) (by simp [tendsto_tan_pi_div_two, this])

lemma tan_surjective : function.surjective tan :=
λ x, surj_on_tan.subset_range trivial

lemma image_tan_Ioo : tan '' (Ioo (-(π / 2)) (π / 2)) = univ :=
univ_subset_iff.1 surj_on_tan

/-- `real.tan` as an `order_iso` between `(-(π / 2), π / 2)` and `ℝ`. -/
def tan_order_iso : Ioo (-(π / 2)) (π / 2) ≃o ℝ :=
(strict_mono_incr_on_tan.order_iso _ _).trans $ (order_iso.set_congr _ _ image_tan_Ioo).trans
  order_iso.set.univ

/-- Inverse of the `tan` function, returns values in the range `-π / 2 < arctan x` and
`arctan x < π / 2` -/
@[pp_nodot] noncomputable def arctan (x : ℝ) : ℝ :=
tan_order_iso.symm x

@[simp] lemma tan_arctan (x : ℝ) : tan (arctan x) = x :=
tan_order_iso.apply_symm_apply x

lemma arctan_mem_Ioo (x : ℝ) : arctan x ∈ Ioo (-(π / 2)) (π / 2) :=
subtype.coe_prop _

lemma arctan_tan {x : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2) : arctan (tan x) = x :=
subtype.ext_iff.1 $ tan_order_iso.symm_apply_apply ⟨x, hx₁, hx₂⟩

lemma cos_arctan_pos (x : ℝ) : 0 < cos (arctan x) :=
cos_pos_of_mem_Ioo $ arctan_mem_Ioo x

lemma cos_sq_arctan (x : ℝ) : cos (arctan x) ^ 2 = 1 / (1 + x ^ 2) :=
by rw [one_div, ← inv_one_add_tan_sq (cos_arctan_pos x).ne', tan_arctan]

lemma sin_arctan (x : ℝ) : sin (arctan x) = x / sqrt (1 + x ^ 2) :=
by rw [← tan_div_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma cos_arctan (x : ℝ) : cos (arctan x) = 1 / sqrt (1 + x ^ 2) :=
by rw [one_div, ← inv_sqrt_one_add_tan_sq (cos_arctan_pos x), tan_arctan]

lemma arctan_lt_pi_div_two (x : ℝ) : arctan x < π / 2 :=
(arctan_mem_Ioo x).2

lemma neg_pi_div_two_lt_arctan (x : ℝ) : -(π / 2) < arctan x :=
(arctan_mem_Ioo x).1

lemma arctan_eq_arcsin (x : ℝ) : arctan x = arcsin (x / sqrt (1 + x ^ 2)) :=
eq.symm $ arcsin_eq_of_sin_eq (sin_arctan x) (mem_Icc_of_Ioo $ arctan_mem_Ioo x)

lemma arcsin_eq_arctan {x : ℝ} (h : x ∈ Ioo (-(1:ℝ)) 1) :
  arcsin x = arctan (x / sqrt (1 - x ^ 2)) :=
begin
  rw [arctan_eq_arcsin, div_pow, sq_sqrt, one_add_div, div_div_eq_div_mul,
      ← sqrt_mul, mul_div_cancel', sub_add_cancel, sqrt_one, div_one];
  nlinarith [h.1, h.2],
end

@[simp] lemma arctan_zero : arctan 0 = 0 :=
by simp [arctan_eq_arcsin]

lemma arctan_eq_of_tan_eq {x y : ℝ} (h : tan x = y) (hx : x ∈ Ioo (-(π / 2)) (π / 2)) :
  arctan y = x :=
inj_on_tan (arctan_mem_Ioo _) hx (by rw [tan_arctan, h])

@[simp] lemma arctan_one : arctan 1 = π / 4 :=
arctan_eq_of_tan_eq tan_pi_div_four $ by split; linarith [pi_pos]

@[simp] lemma arctan_neg (x : ℝ) : arctan (-x) = - arctan x :=
by simp [arctan_eq_arcsin, neg_div]

@[continuity]
lemma continuous_arctan : continuous arctan :=
continuous_subtype_coe.comp tan_order_iso.to_homeomorph.continuous_inv_fun

lemma continuous_at_arctan {x : ℝ} : continuous_at arctan x := continuous_arctan.continuous_at

/-- `real.tan` as a `local_homeomorph` between `(-(π / 2), π / 2)` and the whole line. -/
def tan_local_homeomorph : local_homeomorph ℝ ℝ :=
{ to_fun := tan,
  inv_fun := arctan,
  source := Ioo (-(π / 2)) (π / 2),
  target := univ,
  map_source' := maps_to_univ _ _,
  map_target' := λ y hy, arctan_mem_Ioo y,
  left_inv' := λ x hx, arctan_tan hx.1 hx.2,
  right_inv' := λ y hy, tan_arctan y,
  open_source := is_open_Ioo,
  open_target := is_open_univ,
  continuous_to_fun := continuous_on_tan_Ioo,
  continuous_inv_fun := continuous_arctan.continuous_on }

@[simp] lemma coe_tan_local_homeomorph : ⇑tan_local_homeomorph = tan := rfl
@[simp] lemma coe_tan_local_homeomorph_symm : ⇑tan_local_homeomorph.symm = arctan := rfl

lemma has_strict_deriv_at_arctan (x : ℝ) : has_strict_deriv_at arctan (1 / (1 + x^2)) x :=
have A : cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
by simpa [cos_sq_arctan]
  using tan_local_homeomorph.has_strict_deriv_at_symm trivial (by simpa) (has_strict_deriv_at_tan A)

lemma has_deriv_at_arctan (x : ℝ) : has_deriv_at arctan (1 / (1 + x^2)) x :=
(has_strict_deriv_at_arctan x).has_deriv_at

lemma differentiable_at_arctan (x : ℝ) : differentiable_at ℝ arctan x :=
(has_deriv_at_arctan x).differentiable_at

lemma differentiable_arctan : differentiable ℝ arctan := differentiable_at_arctan

@[simp] lemma deriv_arctan : deriv arctan = (λ x, 1 / (1 + x^2)) :=
funext $ λ x, (has_deriv_at_arctan x).deriv

lemma times_cont_diff_arctan {n : with_top ℕ} : times_cont_diff ℝ n arctan :=
times_cont_diff_iff_times_cont_diff_at.2 $ λ x,
have cos (arctan x) ≠ 0 := (cos_arctan_pos x).ne',
tan_local_homeomorph.times_cont_diff_at_symm_deriv (by simpa) trivial (has_deriv_at_tan this)
  (times_cont_diff_at_tan.2 this)

end real

section
/-!
### Lemmas for derivatives of the composition of `real.arctan` with a differentiable function

In this section we register lemmas for the derivatives of the composition of `real.arctan` with a
differentiable function, for standalone use and use with `simp`. -/

open real

section deriv

variables {f : ℝ → ℝ} {f' x : ℝ} {s : set ℝ}

lemma has_strict_deriv_at.arctan (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') x :=
(real.has_strict_deriv_at_arctan (f x)).comp x hf

lemma has_deriv_at.arctan (hf : has_deriv_at f f' x) :
  has_deriv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') x :=
(real.has_deriv_at_arctan (f x)).comp x hf

lemma has_deriv_within_at.arctan (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) * f') s x :=
(real.has_deriv_at_arctan (f x)).comp_has_deriv_within_at x hf

lemma deriv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  deriv_within (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) * (deriv_within f s x) :=
hf.has_deriv_within_at.arctan.deriv_within hxs

@[simp] lemma deriv_arctan (hc : differentiable_at ℝ f x) :
  deriv (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) * (deriv f x) :=
hc.has_deriv_at.arctan.deriv

end deriv

section fderiv

variables {E : Type*} [normed_group E] [normed_space ℝ E] {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E}
  {s : set E} {n : with_top ℕ}

lemma has_strict_fderiv_at.arctan (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') x :=
(has_strict_deriv_at_arctan (f x)).comp_has_strict_fderiv_at x hf

lemma has_fderiv_at.arctan (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_at x hf

lemma has_fderiv_within_at.arctan (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ x, arctan (f x)) ((1 / (1 + (f x)^2)) • f') s x :=
(has_deriv_at_arctan (f x)).comp_has_fderiv_within_at x hf

lemma fderiv_within_arctan (hf : differentiable_within_at ℝ f s x)
  (hxs : unique_diff_within_at ℝ s x) :
  fderiv_within ℝ (λ x, arctan (f x)) s x = (1 / (1 + (f x)^2)) • (fderiv_within ℝ f s x) :=
hf.has_fderiv_within_at.arctan.fderiv_within hxs

@[simp] lemma fderiv_arctan (hc : differentiable_at ℝ f x) :
  fderiv ℝ (λ x, arctan (f x)) x = (1 / (1 + (f x)^2)) • (fderiv ℝ f x) :=
hc.has_fderiv_at.arctan.fderiv

lemma differentiable_within_at.arctan (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ x, real.arctan (f x)) s x :=
hf.has_fderiv_within_at.arctan.differentiable_within_at

@[simp] lemma differentiable_at.arctan (hc : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ x, arctan (f x)) x :=
hc.has_fderiv_at.arctan.differentiable_at

lemma differentiable_on.arctan (hc : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ x, arctan (f x)) s :=
λ x h, (hc x h).arctan

@[simp] lemma differentiable.arctan (hc : differentiable ℝ f) :
  differentiable ℝ (λ x, arctan (f x)) :=
λ x, (hc x).arctan

lemma times_cont_diff_at.arctan (h : times_cont_diff_at ℝ n f x) :
  times_cont_diff_at ℝ n (λ x, arctan (f x)) x :=
times_cont_diff_arctan.times_cont_diff_at.comp x h

lemma times_cont_diff.arctan (h : times_cont_diff ℝ n f) :
  times_cont_diff ℝ n (λ x, arctan (f x)) :=
times_cont_diff_arctan.comp h

lemma times_cont_diff_within_at.arctan (h : times_cont_diff_within_at ℝ n f s x) :
  times_cont_diff_within_at ℝ n (λ x, arctan (f x)) s x :=
times_cont_diff_arctan.comp_times_cont_diff_within_at h

lemma times_cont_diff_on.arctan (h : times_cont_diff_on ℝ n f s) :
  times_cont_diff_on ℝ n (λ x, arctan (f x)) s :=
times_cont_diff_arctan.comp_times_cont_diff_on h

end fderiv
end
