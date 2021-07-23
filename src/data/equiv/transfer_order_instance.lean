/-
Copyright (c) 2021 Julian Berman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Berman
-/
import data.equiv.basic

universes u v
variables {α : Type u} {β : Type v}

namespace equiv


section instances

variables (e : α ≃ β)

/-!
# Transfer order structures across `equiv`s

Similar to `data.equiv.transfer_algebra_structure`, in this file we prove theorems of the form: if
`β` has an order structure and `α ≃ β` then `α` has an order structure, for preorders, partial
orders, and so on.

Note that most of these constructions can also be obtained using the `transport` tactic.

## Tags

equiv, preorder, partial order, linear order
-/

end instances
end equiv
