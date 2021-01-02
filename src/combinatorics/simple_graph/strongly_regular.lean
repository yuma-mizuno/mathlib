/-
Copyright (c) 2021 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Alena Gusakov
-/
import combinatorics.simple_graph.basic
/-!
# Strongly regular graphs

This module defines strongly regular graphs on a vertex type `V` as

## Main definitions

* `(G : simple_graph V) (G : srg n k l m)` is a `simple_graph` that has properties
  * `fintype.card V = n`
  * `G.is_regular_of_degree k`

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
universes u

namespace simple_graph
variables {V : Type u} [fintype V]
variables (G : simple_graph V)

/-
* have `fintype.card V = n`
* have `is_regular_of_degree k`
-/

def common_verts (v w : V) : set V := (G.neighbor_set v) ∩ (G.neighbor_set w)
-- don't even know if i need this definition but i feel like it'll make things a bit easier?

lemma common_verts_eq_inter (v w : V) : G.common_verts v w = (G.neighbor_set v) ∩ (G.neighbor_set w) := rfl

lemma not_mem_left_common_verts (v w : V) : v ∉ (G.common_verts v w) :=
begin
  rw common_verts,
  simp only [set.mem_inter_eq, irrefl, mem_neighbor_set, not_false_iff, false_and],
end

lemma not_mem_right_common_verts (v w : V) : w ∉ (G.common_verts v w) :=
begin
  rw common_verts,
  simp,
end

variables  [locally_finite G]

/--
A graph is strongly regular with parameters `n k l m` if
 * its vertex set has cardinality `n`
 * it is regular with degree `k`
 * every pair of adjacent vertices has `l` common neighbors
 * every pair of nonadjacent vertices has `m` common neighbors
-/
structure is_SRG_of (n k l m : ℕ) : Prop :=
(card : fintype.card V = n)
(regular : G.is_regular_of_degree k)
(adj_common : ∀ (v w : V), G.adj v w → fintype.card (G.common_verts v w) = l)
(nadj_common : ∀ (v w : V), ¬ G.adj v w → fintype.card (G.common_verts v w) = m)

-- i didn't think i'd get this far, now what
lemma degree_lt_card_verts (G : simple_graph V) (v : V) : G.degree v < fintype.card V :=
begin
  classical,
  rw ← finset.card_univ,
  rw degree,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use v,
  split,
  { simp },
  { apply finset.subset_univ },
end

variables [nonempty V]

lemma is_regular_degree_lt_card_verts (G : simple_graph V) (k : ℕ) (h : G.is_regular_of_degree k) :
  k < fintype.card V :=
begin
  rw is_regular_of_degree at h,
  inhabit V,
  specialize h (default V),
  rw ← h,
  apply degree_lt_card_verts,
end

-- some nice simp lemmas could include
  -- in general, fintype.card (G.common_verts v w) ≤ G.degree v
  -- for G.adj v w, fintype.card (G.common_verts v w) < G.degree v

lemma common_verts_subset_neighbor_set (v w : V) : G.common_verts v w ⊆ G.neighbor_set v :=
begin
  rw common_verts_eq_inter,
  exact set.inter_subset_left _ _,
end

lemma set.to_finset_subset_to_finset_iff (α : Type*) (s t : set α) [fintype s] [fintype t] : s ⊆ t ↔ s.to_finset ⊆ t.to_finset :=
⟨λ h x hx, set.mem_to_finset.mpr $ h $ set.mem_to_finset.mp hx, λ h x hx, set.mem_to_finset.mp $ h $ set.mem_to_finset.mpr hx⟩

lemma card_common_verts_le_degree (v w : V) : fintype.card (G.common_verts v w) ≤ G.degree v :=
begin
  rw degree,
  have h := G.common_verts_subset_neighbor_set v w,

  rw common_verts,
  rw ← set.to_finset_card,
  apply finset.card_le_of_subset,
  rw common_verts at h,
  rw neighbor_finset,
  rw ← set.to_finset_subset_to_finset_iff _ _,
  exact h,
end

-- this works for both `G.adj v w` and `¬ G.adj v w`, good job me
lemma card_common_verts_lt_card_verts (G : simple_graph V) (v w : V) :
  fintype.card (G.common_verts v w) < fintype.card V :=
begin
  classical,
  have h := not_mem_left_common_verts G v w,
  rw ← set.to_finset_card,
  rw ← finset.card_univ,
  --rw common_verts,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use v,
  split,
  { simp,
    exact h },
  { apply finset.subset_univ },
end

-- maybe more lemmas could be done that say
  -- card common_verts v w = x for all v w → G.is_regular_of_degree k for some k? is that even true?

lemma adj_card_common_verts_lt_degree (v w : V) (h : G.adj v w) : fintype.card (G.common_verts v w) < G.degree v :=
begin
  classical,
  rw degree,
  rw ← set.to_finset_card,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    exact not_mem_right_common_verts G v w },
  { rw finset.insert_subset,
    split,
    { simpa },
    { rw neighbor_finset,
      rw ← set.to_finset_subset_to_finset_iff,
      exact common_verts_subset_neighbor_set G v w } },
end

lemma card_common_verts_le_regular_degree (v w : V) (k : ℕ) (h : G.is_regular_of_degree k) :
  fintype.card (G.common_verts v w) ≤ k :=
begin
  rw is_regular_of_degree at h,
  specialize h v,
  rw ← h,
  exact card_common_verts_le_degree G v w
end

lemma adj_card_common_verts_lt_regular_degree (v w : V) (h : G.adj v w) (k : ℕ) (h2 : G.is_regular_of_degree k) :
  fintype.card (G.common_verts v w) < k :=
begin
  rw is_regular_of_degree at h2,
  specialize h2 v,
  rw ← h2,
  exact G.adj_card_common_verts_lt_degree v w h,
end


-- lemma idea 1:
-- The four parameters in an srg(n, k, λ, μ) are not independent and must obey the following relation:
-- `(n - k - 1)m = k(k - l - 1)`
-- now subtraction is bad, so how would one deal with this
  -- (`is_regular_degree_lt_card_verts`) k < n
  -- (`card_common_verts_lt_card_verts`) l < n
  -- (`card_common_verts_lt_card_verts`) m < n
  -- (`adj_card_common_verts_lt_regular_degree`) l < k
  -- (`card_common_verts_le_regular_degree`) m ≤ k (this is the one where ≤ makes sense)

-- lemma idea 2:
-- if I is identity and J is all-one matrix, then adj matrix A of SRG obeys relation
  -- A^2 = kI + lA + m(J - I - A)


end simple_graph
