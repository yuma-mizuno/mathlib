/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import linear_algebra.direct_sum_module

/-!
# Graded rings and algebras

Let `ι` be an additive monoid.

Let `A` be a ring. A grading on `A` is a family of subgroups `G i`
of `A` indexed by `G`, with the following properties:

* `1 ∈ G 0`
* If `a ∈ G i` and `b ∈ G j` then `a*b ∈ G (i + j)`
* The induced map `⨁ᵢ G i → A` is a bijection (equivalently, a ring isomorphism).

Variant: `R` is a commutative ring, `A` is an `R`-algebra
and all the `G i` are `R`-submodules of `M`.

## Implementation notes

## References

https://stacks.math.columbia.edu/tag/00JL

-/

variables (ι : Type*) [add_monoid ι] (A : Type*) [ring A]
  (G : ι → add_subgroup A)

/-- The `direct_sum` formed by a collection of `submodule`s of `M` is said to be internal if the
canonical map `(⨁ i, A i) →ₗ[R] M` is bijective. -/
def direct_sum.submodule_is_internal {R M : Type*}
  [semiring R] [add_comm_monoid M] [module R M]
  (A : ι → submodule R M) : Prop :=
function.bijective (to_module R ι M (λ i, (A i).subtype))
