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
λ X _ f H,
begin
  resetI,
  rw continuous_iff_continuous_at,
  intros x V hV,
  rcases H x with ⟨U, hx, h⟩,
  convert h.tendsto ⟨x, hx⟩ hV using 2,
  exact congr_arg (filter.map f) (map_nhds_subtype_val_eq _ (mem_nhds_sets U.2 hx)).symm,
end
