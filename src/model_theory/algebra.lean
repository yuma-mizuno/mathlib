/-
Copyright (c) 2021 Aaron Anderson All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import model_theory.basic

/-!
## First-Order Structures in Algebra
This file places first-order logic instances on objects from the algebra library.

-/

namespace first_order
namespace language

variable {M : Type*}

/- The constant portion in the monoid language. -/
inductive monoid_consts : Type
| one : monoid_consts

/- The function portion of the monoid language. -/
inductive monoid_functions : ℕ → Type
| mul : monoid_functions 1

/-- The language of monoids -/
def of_monoids : language := ⟨monoid_consts, monoid_functions, λ _, pempty⟩

instance monoid_structure [has_one M] [has_mul M] : language.of_monoids.Structure M :=
⟨λ _, 1, λ n f, begin
  cases f,
  exact ((*) : M → M → M)
end, λ n R, R.elim⟩

/- The function portion of the group language. -/
inductive group_functions : ℕ → Type
| neg : group_functions 0
| mul : group_functions 1

/-- The language of groups -/
def of_groups : language := ⟨monoid_consts, group_functions, λ _, pempty⟩

instance group_structure [has_one M] [has_mul M] [has_neg M] : language.of_groups.Structure M :=
⟨λ _, 1, λ n f, begin
  cases f,
  { exact λ x, - x },
  { exact ((*) : M → M → M) }
end, λ n R, R.elim⟩

inductive ring_consts : Type
| zero : ring_consts
| one : ring_consts

/- The function portion of the semiring language. -/
inductive semiring_functions : ℕ → Type
| add : semiring_functions 1
| mul : semiring_functions 1

/-- The language of semirings -/
def of_semirings : language := ⟨ring_consts, semiring_functions, λ _, pempty⟩

instance semiring_structure [has_zero M] [has_one M] [has_add M] [has_mul M] :
  language.of_semirings.Structure M :=
⟨λ c, begin
  cases c,
  { exact 0 },
  { exact 1 }
end, λ n f, begin
  cases f,
  { exact ((+) : M → M → M) },
  { exact ((*) : M → M → M) }
end, λ n R, R.elim⟩

/- The function portion of the ring language. -/
inductive ring_functions : ℕ → Type
| neg : ring_functions 0
| add : ring_functions 1
| mul : ring_functions 1

/-- The language of rings -/
def of_rings : language := ⟨ring_consts, ring_functions, λ _, pempty⟩

instance ring_structure [has_zero M] [has_one M] [has_add M] [has_mul M] [has_neg M] :
  language.of_rings.Structure M :=
⟨λ c, begin
  cases c,
  { exact 0 },
  { exact 1 }
end, λ n f, begin
  cases f,
  { exact λ x, - x },
  { exact ((+) : M → M → M) },
  { exact ((*) : M → M → M) }
end, λ n R, R.elim⟩

end language
end first_order
