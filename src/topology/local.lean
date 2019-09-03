import topology.basic
import topology.opens

open topological_space

/-- We say a predicate on functions on some topological space is "local" if it suffices to
check it on the restriction of the function to some open neighbourhood of each point.

The collections of functions satisfying some local predicate automatically form a sheaf.
-/
def local_pred {τ : Type*} (P : Π {α : Type*} [topological_space α], (α → τ) → Prop) : Prop :=
∀ (α : Type*) [topological_space α] (f : α → τ),
  by exactI (∀ (x : α), ∃ (U : opens α) (m : x ∈ U), P (f ∘ (subtype.val : U → α))) →
  P f

/-- Continuity is a local predicate (on functions with any fixed target topological space). -/
theorem continuous_local {τ : Type*} [topological_space τ] :
  local_pred (λ α _ (f : α → τ), by exactI continuous f) :=
λ α _ f h,
begin
  resetI,
  intros s o,
  -- For each `x`, we take a nbhd `U x` on which we're promised `f` is continuous.
  let U := λ x : α, classical.some (h x),
  -- We define `V x` to be the preimage of s under the restriction of `f` to `U x`.
  let V' := λ x : α, (f ∘ (subtype.val : U x → α)) ⁻¹' s,
  let V := λ x : α, subtype.val '' (V' x),
  -- Now we show that each `V x` is open (being an open subset of `U x`, by the promised continuity).
  have V_open : ∀ x, is_open (V x), sorry,
  -- And finally that `f ⁻¹' s` is the union of the `V x`.
  have eq_union : f ⁻¹' s = ⨆ x, V x, sorry,
  -- Now it's just that unions of opens are open.
  rw eq_union,
  sorry
end
