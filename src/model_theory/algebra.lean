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

/- The functions in the language of monoids. -/
inductive monoid_functions : ℕ → Type
| zero : monoid_functions 0
| plus : monoid_functions 2

/-- The language of monoids -/
def of_monoids : language := ⟨monoid_functions, λ _, pempty⟩

instance monoid_structure [has_one M] [has_mul M] : language.of_monoids.Structure M :=
⟨λ n f, begin
  cases f,
  { exact λ _, 1, },
  { exact binary_fun_map (*) }
end, λ n R, R.elim⟩

end language
end first_order
