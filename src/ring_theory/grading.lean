/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
import algebra.monoid_algebra -- to check we can grade a monoid algebra
import data.polynomial -- to check we can grade a polynomial ring
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

/-!

## test : grading a polynomial ring

I try three ways to do it.

-/


section polynomials

open polynomial

/-!

### First method

Here's the first way: an injective and surjective version

-/

noncomputable example (R : Type*) [semiring R] : add_monoid_grading ℕ (polynomial R) := {
  graded_piece := λ n, add_monoid_hom.mrange (monomial n).to_add_monoid_hom,
  grading_one := ⟨1, set.mem_univ _, rfl⟩,
  grading_mul := begin
    rintros m n - - ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    refine ⟨a * b, set.mem_univ _, (monomial_mul_monomial m n a b).symm⟩,
  end,
  direct_sum := begin
    -- This injectivity proof below doesn't look like much fun
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

/-!

### Second method

An independent and span version. Here we need to prove two lemmas first,
which may or may not be tricky, and we still don't know if the method is any easier.

-/

section equivalence

variables {ι : Type*} [decidable_eq ι] (R : Type) [add_comm_monoid R] (f : ι → add_submonoid R)

theorem direct_sum.to_add_monoid_injective {M : Type*} [add_comm_monoid M]
  (A : ι → add_submonoid M) :
  function.injective ⇑(direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M) ↔
  complete_lattice.independent A :=
begin
  sorry
end

theorem direct_sum.to_add_monoid_surjective {M : Type*} [add_comm_monoid M]
  (A : ι → add_submonoid M) :
  function.surjective ⇑(direct_sum.to_add_monoid (λ i, (A i).subtype) : (⨁ i, A i) →+ M) ↔
  (Sup (set.range A) = ⊤) :=
begin
  sorry
end

theorem direct_sum.add_submonoid_is_internal_iff_independent_and_span :
  direct_sum.add_submonoid_is_internal f ↔
  complete_lattice.independent f ∧ (Sup (set.range f) = ⊤) :=
and_congr (direct_sum.to_add_monoid_injective f) (direct_sum.to_add_monoid_surjective f)

end equivalence

-- second approach
noncomputable example (R : Type*) [semiring R] : add_monoid_grading ℕ (polynomial R) := {
  graded_piece := λ n, add_monoid_hom.mrange (monomial n).to_add_monoid_hom,
  grading_one := ⟨1, set.mem_univ _, rfl⟩,
  grading_mul := begin
    rintros m n - - ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    refine ⟨a * b, set.mem_univ _, (monomial_mul_monomial m n a b).symm⟩,
  end,
  direct_sum := begin
    rw direct_sum.add_submonoid_is_internal_iff_independent_and_span,
    split,
    { rintros n f hf,
      rw add_submonoid.mem_inf at hf,
      cases hf with hfn hfm,
      ext m,
      rw coeff_zero,
      by_cases hmn : m = n,
      { subst hmn,
        dsimp only at hfm,
        --rw mem_supr: missing.
        sorry },
      sorry,
    },
    { sorry }
  end,
   }

/-!

### Third method: prove bijectivity by writing down an inverse function

-/

noncomputable abbreviation monomial.submonoid (R : Type) [semiring R] (i : ℕ) : add_submonoid (polynomial R) :=
(monomial i : R →ₗ polynomial R).to_add_monoid_hom.mrange

noncomputable abbreviation monomial.to_submonoid (R : Type) [semiring R] (i : ℕ) : R →+ monomial.submonoid R i :=
(monomial i : R →ₗ polynomial R).to_add_monoid_hom.mrange_restrict

-- noncomputable def polynomial_equiv (R : Type) [semiring R] :
--   (⨁ i, monomial.submonoid R i) ≃+ polynomial R :=
-- add_monoid_hom.to_add_equiv
--   (direct_sum.to_add_monoid $ λ i,
--     (monomial.submonoid R i).subtype)
--   (finsupp.lift_add_hom $ λ n,
--     (direct_sum.of (λ i, monomial.submonoid R i) n).comp (monomial.to_submonoid R n))
--   (begin
--     ext i ⟨x, r, _, rfl⟩ : 2,
--     dsimp,
--     simp [monomial],
--     refl, -- fails on this branch
--   end)
--   (begin
--     ext i r : 2,
--     dsimp,
--     simp [monomial],
--   end)

noncomputable def polynomial_equiv (R : Type) [semiring R] :
  (⨁ i, monomial.submonoid R i) ≃+ polynomial R  :=
{ inv_fun := sorry, -- WARNING: sorried data! This is the inverse function.
  left_inv := sorry, -- This may or may not be tricky
  right_inv := sorry, -- this may or may not be tricky.
  ..(direct_sum.to_add_monoid
    (λ i, (monomial.submonoid R i).subtype) : (⨁ i, monomial.submonoid R i) →+ _) }

noncomputable example (R : Type*) [semiring R] : add_monoid_grading ℕ (polynomial R) := {
  graded_piece := λ n, add_monoid_hom.mrange (monomial n).to_add_monoid_hom,
  grading_one := ⟨1, set.mem_univ _, rfl⟩,
  grading_mul := begin
    rintros m n - - ⟨a, -, rfl⟩ ⟨b, -, rfl⟩,
    refine ⟨a * b, set.mem_univ _, (monomial_mul_monomial m n a b).symm⟩,
  end,
  direct_sum := begin
    exact equiv.bijective (polynomial_equiv R).to_equiv,
  end }

end polynomials

-- second test case (I've not begun to think about it): grading add_monoid_algebras.
example (R : Type*) [semiring R] (M : Type*) [add_monoid M] [decidable_eq M] :
  add_monoid_grading M (add_monoid_algebra R M) := sorry
