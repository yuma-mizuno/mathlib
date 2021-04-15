/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
import algebra.monoid_algebra -- to check we can grade a monoid algebra
import data.polynomial.basic -- to check we can grade a polynomial ring
/-!

# Grading of a ring by a monoid

-/

/-- If `M` is an additive monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₀` and `Rₘ*Rₙ ⊆ R_{m+n}` -/
structure add_monoid_grading (M : Type*) [add_monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(graded_piece : M → add_submonoid R)
(direct_sum : direct_sum.add_submonoid_is_internal graded_piece)
(grading_one : (1 : R) ∈ graded_piece 0)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ graded_piece m → s ∈ graded_piece n → r * s ∈ graded_piece (m + n))

/-- If `M` is a monoid, then an `M`-grading on a ring `R` is a decomposition of `R` as
    an internal direct sum `R = ⨁Rₘ` into submonoids indexed by `m : M`, where the decomposition
    respects `1` and `*`, in the sense that `1 ∈ R₁` and `Rₘ*Rₙ ⊆ R_{m*n}` -/
structure monoid_grading (M : Type*) [monoid M] [decidable_eq M] (R : Type*) [semiring R] :=
(graded_piece : M → add_submonoid R)
(grading_one : (1 : R) ∈ graded_piece 1)
(grading_mul : ∀ (m n : M) (r s : R),
  r ∈ graded_piece m → s ∈ graded_piece n → r * s ∈ graded_piece (m * n))
(direct : direct_sum.add_submonoid_is_internal graded_piece)

attribute [to_additive] monoid_grading

open_locale direct_sum
-- should be in algebra.direct_sum
lemma direct_sum.to_add_monoid_apply {ι : Type*} [decidable_eq ι]
  {β : ι → Type*} [Π (i : ι), add_comm_monoid (β i)]
  [ Π (i : ι) (x : β i), decidable (x ≠ 0)]
  {γ : Type*} [add_comm_monoid γ]
  (f : Π (i : ι), β i →+ γ) (b : ⨁ i, β i):
  direct_sum.to_add_monoid f b = dfinsupp.sum b (λ i, f i) :=
dfinsupp.sum_add_hom_apply _ _

open polynomial

noncomputable example (R : Type*) [semiring R] : add_monoid_grading ℕ (polynomial R) := {
  graded_piece := λ n, add_monoid_hom.mrange (monomial n).to_add_monoid_hom,
  grading_one := ⟨1, set.mem_univ _, rfl⟩,
  grading_mul := begin
    rintros m n - - ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    refine ⟨a * b, set.mem_univ _, (monomial_mul_monomial m n a b).symm⟩,
  end,
  direct_sum := begin
    split,
    { intros a b h,
      ext,
      rw ext_iff at h,
      classical,
      simp only [direct_sum.to_add_monoid_apply, add_submonoid.coe_subtype] at h,
      by_cases hin : i = n,
      { sorry },
      sorry,
    },
    { sorry }
  end,
   }
