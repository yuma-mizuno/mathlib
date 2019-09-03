import topology.basic
import topology.opens

open topological_space

/-- We say a predicate on functions between topological spaces is "local" if it suffices to
check it on the restriction of the function to some open neighbourhood of each point.

The collections of functions satisfying some local predicate automatically form a sheaf.
-/
def local_pred (P : Π {α β : Type*} [topological_space α] [topological_space β], (α → β) → Prop) : Prop :=
∀ (α β : Type*) [topological_space α] [topological_space β] (f : α → β),
  by exactI (∀ (x : α), ∃ (U : opens α) (m : x ∈ U), P (f ∘ (subtype.val : U → α))) →
  P f

/-- A subset of a subtype can be thought of as a subset of the type. -/
def set_of_subtype_set {α : Type*} {P : α → Prop} (x : set {a : α // P a}) : set α :=
{a : α | ∃ (h : P a), (⟨a,h⟩ : {a : α // P a}) ∈ x}

/-- Continuity is a local predicate. -/
theorem continuous_local : local_pred @continuous :=
λ α β _ _ f h,
begin
  resetI,
  intros s o,
  -- For each `x`, we take a nbhd `U x` on which we're promised `f` is continuous.
  let U := λ x : α, classical.some (h x),
  -- We define `V x` to be the preimage of s under the restriction of `f` to `U x`.
  let V' := λ x : α, (f ∘ (subtype.val : U x → α)) ⁻¹' s,
  let V := λ x : α, set_of_subtype_set (V' x),
  -- Now we show that each `V x` is open (being an open subset of `U x`, by the promised continuity).
  have V_open : ∀ x, is_open (V x), sorry,
  -- And finally that `f ⁻¹' s` is the union of the `V x`.
  have eq_union : f ⁻¹' s = ⨆ x, V x, sorry,
  -- Now it's just that unions of opens are open.
  rw eq_union,
  sorry
end
