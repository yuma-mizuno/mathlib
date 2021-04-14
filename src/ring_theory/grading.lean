/-
Copyright (c) 2021 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
import algebra.direct_sum
/-!

# Grading of a ring by a monoid

-/
#check direct_sum.add_submonoid_is_internal

#exit

Adam:

def foo {A : Type*} [add_comm_group A] {ι : Type*}
  (f : ι → add_subgroup A) : (⨁ i, f i) →+ A :=
dfinsupp.sum_add_hom (λ i : ι, (f i).subtype)

structure grading (M : Type*) (A : Type*) [add_comm_group A] :=
(graded_part : M → add_subgroup A)
(iso : function.bijective $ foo graded_part)

structure graded_ring (M : Type*) [add_monoid M] (A : Type*) [ring A]
  extends grading M A :=
(grading_one : (1 : A) ∈ graded_part 0)
(grading_mul {r s m n} :
  r ∈ graded_part m → s ∈ graded_part n → (r * s) ∈ graded_part (m+n))

End of Adam


  /-
  def independent' {ι : Sort*} {α : Type*} [complete_lattice α] (s : ι → α): Prop :=
∀ ⦃i : ι⦄, disjoint (s i) (⨆ (j ≠ i), s j)
-/
