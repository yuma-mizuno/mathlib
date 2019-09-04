import topology.basic
import topology.opens
import tactic.tidy

universes u₁ u₂ u₃

open topological_space

-- TODO existing short names?
def left {X : Type*} (U V : set X) : U ∩ V → U :=
begin
  rintro ⟨x, ⟨h, _⟩⟩,
  exact ⟨x, h⟩
end

def right {X : Type*} (U V : set X) : U ∩ V → V :=
begin
  rintro ⟨x, ⟨_, h⟩⟩,
  exact ⟨x, h⟩
end


/-- We say a predicate on functions on some topological space is "local" if it suffices to
check it on the restriction of the function to some open neighbourhood of each point.

The collections of functions satisfying some local predicate automatically form a sheaf.
-/
def local_pred {τ : Type u₂} (P : Π {α : Type u₁} [topological_space α], (α → τ) → Prop) : Prop :=
∀ (α : Type*) [topological_space α] (f : α → τ),
  by exactI (∀ (x : α), ∃ (U : opens α) (m : x ∈ U), P (f ∘ (subtype.val : U → α))) →
  P f

attribute [class] local_pred

/-- Continuity is a local predicate (on functions with any fixed target topological space). -/
instance continuous_local {τ : Type u₂} [topological_space τ] :
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


variables {X : Type u₁} {Y : Type u₂} {ι : Type u₃} {U : ι → set X}

-- TODO is there an existing short name?
def glom {i : ι} (x : U i) : ((⨆ i, U i) : set X) :=
set.inclusion (lattice.le_supr U i) x

namespace glue
noncomputable def pick (x : ⨆ i, U i) : ι :=
classical.some (classical.some (classical.some_spec x.2))

lemma mem_pick (x : ⨆ i, U i) : x.1 ∈ U (glue.pick x) :=
begin
  convert classical.some_spec (classical.some_spec x.2),
  rw ← classical.some_spec (classical.some (classical.some_spec x.2)),
  refl
end
end glue

noncomputable def glue (f : Π i, U i → Y) (h : Π i j, f i ∘ left _ _ = f j ∘ right _ _) : (⨆ i, U i) → Y :=
λ x, f (glue.pick x) ⟨x, glue.mem_pick x⟩

lemma glue.spec (f : Π i, U i → Y) (h : Π i j, f i ∘ left _ _ = f j ∘ right _ _) {i : ι} (x : U i) :
glue f h (glom x) = f i x :=
begin
  convert congr_fun (h _ _) ⟨x.1, ⟨glue.mem_pick (glom x), x.2⟩⟩,
  cases x, congr,
end

lemma glue.spec' (f : Π i, U i → Y) (h : Π i j, f i ∘ left _ _ = f j ∘ right _ _) (i : ι) :
glue f h ∘ set.inclusion (lattice.le_supr U i) = f i :=
begin
  funext, apply glue.spec
end

variables [topological_space X]

section
variables (P : Π {α : Type u₁} [topological_space α], (α → Y) → Prop) [ℒ : local_pred @P]
include ℒ

lemma glue.local_pred (o : ∀ i, is_open (U i)) (f : Π i, U i → Y) (h : Π i j, f i ∘ left _ _ = f j ∘ right _ _) (w : ∀ i, P (f i)) :
  P (glue f h) :=
begin
  apply ℒ,
  intro x,
  have i := glue.pick x,
  have O : opens X := ⟨U i, o i⟩,
  have O' : opens (⨆ i, U i : set X) := sorry,
  use O',
  fsplit,
  sorry,
  have wi := w i,
  rw ← glue.spec' f h i at wi,
  sorry,
end
end

-- TODO it would be nice if this instance could be found...
lemma glue.continuous [topological_space Y] (o : ∀ i, is_open (U i)) (f : Π i, U i → Y) (h : Π i j, f i ∘ left _ _ = f j ∘ right _ _) (w : ∀ i, continuous (f i)) :
  continuous (glue f h) :=
@glue.local_pred _ _ _ _ _ (λ α _ (f : α → Y), by exactI continuous f) continuous_local o f h w
