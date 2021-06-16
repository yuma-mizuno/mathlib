/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import linear_algebra.direct_sum_module
import ring_theory.ideal.basic

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

open direct_sum

structure add_subgroup_grading (ι : Type*) [add_monoid ι] [decidable_eq ι] (A : Type*) [ring A] :=
  (G : ι → add_subgroup A)
  (hG_zero : (1 : A) ∈ G 0)
  (hG_add : ∀ {i j : ι} (a : A) (ha : a ∈ G i) (b : A) (hb : b ∈ G j), a * b ∈ G (i + j))
  (hG : add_subgroup_is_internal G)

namespace add_subgroup_grading

variables {ι : Type*} [add_monoid ι] [decidable_eq ι] {A : Type*} [ring A] (g : add_subgroup_grading ι A)

def component (g : add_subgroup_grading ι A) (i : ι) (a : A) : g.G i := sorry

def is_homogeneous (J : ideal A) : Prop := ∀ (j ∈ J) (i : ι), (component g i j).1 ∈ J

end add_subgroup_grading
