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

#check direct_sum.add_submonoid_is_internal

section equivalence
-- perhaps an easier way of working with direct_sum.add_submonoid_is_internal
variables (ι : Type*) [decidable_eq ι] (R : Type) [add_comm_monoid R] (f : ι → add_submonoid R)

-- this should be two lemmas: the first shouls say that the map defined in
-- `direct_sum.add_submonoid_is_internal` is injective iff independent,
-- and the second says it's surjective iff Sup is top. Then this theorem
-- follows immediately.
theorem direct_sum.add_submonoid_is_internal_iff_independent_and_span :
  direct_sum.add_submonoid_is_internal f ↔
    -- first is injective, second surjective
    complete_lattice.independent f ∧ (Sup (set.range f) = ⊤) :=
sorry

end equivalence

noncomputable example (R : Type*) [semiring R] : add_monoid_grading ℕ (polynomial R) := {
  graded_piece := λ n, add_monoid_hom.mrange (monomial n).to_add_monoid_hom,
  grading_one := ⟨1, set.mem_univ _, rfl⟩,
  grading_mul := begin
    rintros m n - - ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    refine ⟨a * b, set.mem_univ _, (monomial_mul_monomial m n a b).symm⟩,
  end,
  direct_sum := begin
    -- is it easier to rw `direct_sum.add_submonoid_is_internal_iff_independent_and_span`
    -- immediately? This injectivity proof below doesn't look like much fun, but then again
    -- I don't know whether the independence proof looks like much fun either.
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
    -- I didn't think about surjectivity at all but it looks easier
    { sorry }
  end,
   }

example (R : Type*) [semiring R] (M : Type*) [add_monoid M] [decidable_eq M] :
  add_monoid_grading M (add_monoid_algebra R M) := sorry
