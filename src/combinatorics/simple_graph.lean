/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson, Jalex Stark, Kyle Miller.
-/
import data.fintype.basic
import data.sym2
import data.zmod.basic
/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

## Implementation notes

* A locally finite graph is one with instances `∀ v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
is locally finite, too.

TODO: This is the simplest notion of an unoriented graph.  This should
eventually fit into a more complete combinatorics hierarchy which
includes multigraphs and directed graphs.  We begin with simple graphs
in order to start learning what the combinatorics hierarchy should
look like.

TODO: Part of this would include defining, for example, subgraphs of a
simple graph.

-/
open finset

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent edges;
see `simple_graph.E` for the corresponding type of edges.
-/
@[ext] structure simple_graph (V : Type*) :=
(adj : V → V → Prop)
(sym : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
The complete graph on a type `V` is the simple graph with all pairs of distinct vertices adjacent.
-/
def complete_graph (V : Type*) : simple_graph V :=
{ adj := ne }

instance (V : Type*) : inhabited (simple_graph V) :=
⟨complete_graph V⟩

instance complete_graph_adj_decidable (V : Type*) [decidable_eq V] :
  decidable_rel (complete_graph V).adj :=
by { dsimp [complete_graph], apply_instance }

namespace simple_graph
variables {V : Type*} (G : simple_graph V)

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

lemma ne_of_edge {a b : V} (hab : G.adj a b) : a ≠ b :=
by { rintro rfl, exact G.loopless a hab }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.  It is given as a subtype of the symmetric square.
-/
def E : Type* := {x : sym2 V // x ∈ sym2.from_rel G.sym}

/-- Allows us to refer to a vertex being a member of an edge. -/
instance has_mem : has_mem V G.E := { mem := λ v e, v ∈ e.val }

/-- Construct an edge from its endpoints. -/
def edge_of_adj {v w : V} (h : G.adj v w) : G.E := ⟨⟦(v,w)⟧, h⟩

lemma mem_of_adj {v w : V} (h : G.adj v w) :
  v ∈ G.edge_of_adj h := sym2.mk_has_mem v w

lemma mem_of_adj_right {v w : V} (h : G.adj v w) :
  w ∈ G.edge_of_adj h := sym2.mk_has_mem_right v w

lemma adj_iff_exists_edge {v w : V} (hne : v ≠ w) :
  G.adj v w ↔ ∃ (e : G.E), v ∈ e ∧ w ∈ e :=
begin
  split, { intro, use ⟦(v,w)⟧, assumption, refine ⟨(G.mem_of_adj _), (G.mem_of_adj_right _)⟩ },
  rintro ⟨e, ⟨w', hve⟩, ⟨v', hew⟩⟩,
  have : e.val = ⟦(v,w)⟧, { rw [hve, sym2.eq_iff] at hew ⊢, cc },
  have key := e.property, rwa this at key,
end

variables {G}

/-- Given an edge and one vertex incident on it, construct the other one. -/
noncomputable def E.other (e : G.E) {v : V} (h : v ∈ e) : V :=
by { have : v ∈ e.val, apply h, exact this.other }

lemma E.other_mem (e : G.E) {v : V} (h : v ∈ e) : e.other h ∈ e :=
begin
  change sym2.mem.other h ∈ e.val, have := sym2.mem_other_spec h,
  convert sym2.mk_has_mem_right _ _; tauto,
end

lemma E.other_ne (e : G.E) {v : V} (h : v ∈ e) : e.other h ≠ v :=
begin
  have key := e.property,
  erw [← sym2.mem_other_spec h, sym2.eq_swap] at key,
  exact G.ne_of_edge key,
end

attribute [irreducible] E.other
variables (G)

instance E.inhabited [inhabited {p : V × V | G.adj p.1 p.2}] : inhabited G.E :=
⟨begin
  rcases inhabited.default {p : V × V | G.adj p.1 p.2} with ⟨⟨x, y⟩, h⟩,
  use ⟦(x, y)⟧, rwa sym2.from_rel_prop,
end⟩

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.E := subtype.fintype _

attribute [irreducible] E

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

@[symm] lemma edge_symm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.sym x, λ x, G.sym x⟩

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
by tauto

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v : V) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
by simp [neighbor_finset]

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
by simp [degree, neighbor_finset]

end finite_at

section locally_finite

class locally_finite :=
(neighbor_set_fintype' : Π (v : V), fintype (G.neighbor_set v))

variable [locally_finite G]

instance neighbor_set_fintype (v : V) : fintype (G.neighbor_set v) :=
locally_finite.neighbor_set_fintype' v

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

end locally_finite

section finite

variables [fintype V]

instance fintype.locally_finite [decidable_rel G.adj] : locally_finite G :=
⟨λ v, @subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _⟩

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (complete_graph V).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma complete_graph_is_regular [decidable_eq V] :
  (complete_graph V).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

end finite

section maps

variables {W : Type*} (G) (H : simple_graph W)

abbreviation embedding := rel_embedding G.adj H.adj

infix ` ↪g ` : 50 := embedding

abbreviation isomorphism := rel_iso G.adj H.adj

infix ` ≃g ` : 50 := isomorphism

structure homomorphism :=
(to_fun : V → W)
(map_adj' : ∀ i j : V, G.adj i j → H.adj (to_fun i) (to_fun j))

infix ` →g ` : 50 := homomorphism

namespace homomorphism

instance : has_coe_to_fun (G →g H) := ⟨λ _, V → W, to_fun⟩

variables {G} {H} {f : G →g H}

lemma map_adj {i j : V} : G.adj i j → H.adj (f i) (f j) := f.map_adj' i j

end homomorphism

end maps

/-- A constructor that turns a not-necessarily-symmetric, but irreflexive relation into a graph -/
def symmetrize {V : Type*} (r : V → V → Prop) (h : irreflexive r) : simple_graph V :=
{ adj := λ v w, r v w ∨ r w v,
  sym := λ v w h2, by tauto, }

end simple_graph

section examples



/-- The graph with no edges-/
def empty_graph (V : Type*) : simple_graph V := { adj := λ i j, false }

/-- A graph on `n` vertices with `n` edges in a cycle -/
def cycle_graph (n : ℕ) (three_le : 3 ≤ n) : simple_graph (zmod n) :=
simple_graph.symmetrize (λ i j, i = j + 1) (λ v h, begin
  simp only [or_self] at h, symmetry' at h, rw ← sub_eq_zero at h,
    simp only [add_sub_cancel'] at h,
    haveI : fact (1 < n) := lt_of_lt_of_le (by linarith) three_le,
    apply zero_ne_one h.symm,
end)

/-- The complete partite graph on a specified family of types  -/
def complete_partite_graph {ι : Type*} (f : ι → Type*) : simple_graph (Σ i : ι, f i) :=
{ adj := λ v w, v.1 ≠ w.1 }

/-- The complete bipartite graph on a specified family of types -/
def complete_equiv_complete_partite (V : Type*) :
  complete_graph V ≃g complete_partite_graph (λ v : V, punit) := sorry

def single_edge_graph {V : Type*} {v w : V} (hne : v ≠ w) : simple_graph V :=
{ adj := λ i j, (i = v ∧ j = w) ∨ (i = w ∧ j = v) }

end examples

namespace simple_graph
section coloring -- ## Coloring


variables {V : Type*} (k : ℕ) (G : simple_graph V)

def coloring := G →g (empty_graph (fin k))

def colorable : Prop := nonempty (coloring k G)

variables {k} {G}

lemma colorable_of_colorable_of_le {j : ℕ} (hle : j ≤ k) : colorable j G → colorable k G := sorry

theorem colorable_of_degree_le [fintype V] [decidable_rel G.adj]
  (deg_le : ∀ (v : V), G.degree v ≤ k) : colorable (k+1) G := sorry

theorem colorable_complete_partite [fintype V] (f : V → Type*) :
  colorable (fintype.card V) (complete_partite_graph f) := sorry

end coloring

section graph_operations -- ## Graph Operations

variables {V : Type*}

instance : has_union (simple_graph V) :=
⟨λ G H, { adj := λ v w, G.adj v w ∨ H.adj v w,
          sym := λ v w h, by { cases h, { left, exact G.sym h, }, right, exact H.sym h } }⟩

instance : has_inter (simple_graph V) :=
⟨λ G H, { adj := λ v w, G.adj v w ∧ H.adj v w,
          sym := λ v w h, ⟨G.sym h.1, H.sym h.2⟩ }⟩

instance : has_subset (simple_graph V) :=
⟨λ G H, ∀ v w, G.adj v w → H.adj v w⟩

instance : bounded_lattice (simple_graph V) :=
{ le := (⊆),
  sup := (∪),
  inf := (∩),
  bot := empty_graph V,
  top := complete_graph V,
  le_refl := by obviously,
  le_trans := by obviously,
  le_antisymm := by obviously,
  le_inf := by obviously,
  sup_le := by obviously,
  inf_le_left := by obviously,
  inf_le_right := by obviously,
  le_sup_left := λ G H, λ v w h, by { unfold has_sup.sup, unfold has_union.union, left, apply h, },
  le_sup_right := λ G H, λ v w h, by { unfold has_sup.sup, unfold has_union.union, right, apply h, },
  bot_le := by obviously,
  le_top := by obviously, }

/-- Erase an edge of a graph to get a smaller graph -/
def erase_edge (G : simple_graph V) (e : G.E) : simple_graph V :=
{ adj := λ v w, G.adj v w ∧ ¬ (v ∈ e ∧ w ∈ e),
  sym := λ v w h, ⟨G.sym h.1, by { rw and_comm, exact h.2, }⟩, }

/-- Add an edge between two distinct vertices -/
def insert_edge (G : simple_graph V) {v w : V} (hne : v ≠ w) := G ∪ single_edge_graph hne

/-- Contracts an edge by identifying its endpoints -/
def contract (G : simple_graph V) (e : G.E) : simple_graph sorry := sorry

open sum

def subdivide_adj (G : simple_graph V) (e : G.E) : (V ⊕ punit) → (V ⊕ punit) → Prop
| (inl a) (inl b) := (G.erase_edge e).adj a b
| (inl a) _ := a ∈ e
| _ (inl a) := a ∈ e
| _ _ := false

/-- Subdivides an edge by turning it into two edges, with a new vertex in between -/
def subdivide (G : simple_graph V) (e : G.E) : simple_graph (V ⊕ punit) :=
{ adj := G.subdivide_adj e,
  sym := λ v w h, by { cases v; cases w; unfold simple_graph.subdivide_adj at *,
    {apply (G.erase_edge e).sym h}, repeat { assumption }, }, }

end graph_operations

section walking -- ## Walking

def path_graph (n : ℕ) : simple_graph (zmod (n + 1)) :=
simple_graph.symmetrize (λ i j, (i = j + 1 ∧ i ≠ 0))
(λ i, by { by_cases i = 0, {simp [h]},
    simp only [h, and_true, ne.def, not_false_iff, or_self],
    intro con, symmetry' at con, rw ← sub_eq_zero at con,
    simp only [add_sub_cancel'] at con,
    sorry, } )

end walking


section connectivity -- ## Connectivity

variables {V : Type*} (G : simple_graph V)

/-- Determines if two vertices are connected -/
def are_connected : V → V → Prop := eqv_gen G.adj

/-- Quotient of the vertex type by connectivity -/
def connected_components := quotient (eqv_gen.setoid (are_connected G))

/-- Determines if a graph is connected -/
def is_connected : Prop := ∀ v w, G.are_connected v w

end connectivity

section trees

/-- The graph does not contain a cycle -/
def is_acyclic {V : Type*} (G : simple_graph V) : Prop :=
∀ (n : ℕ) (h : 3 ≤ n), (cycle_graph n h ↪g G) → false

/-- A tree is an acyclic connected graph -/
def is_tree {V : Type*} (G : simple_graph V) : Prop := G.is_connected ∧ G.is_acyclic

end trees


end simple_graph
