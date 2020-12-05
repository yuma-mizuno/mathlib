import combinatorics.simple_graph.basic

open simple_graph

/-!
# Subgraphs of a simple graph
-/

universe u
variables {V : Type u} (G : simple_graph V)

/--
A subgraph of a graph is a subset of vertices and a subset of edges
such that each endpoint of an edge is contained in the vertex set.
Subgraphs implement the `simple_graph` class.  They also form a bounded lattice.
Note: subgraphs could also have been defined as in `subgraph.of_edge_set'`.
We prove this alternative definition is equivalent.
-/
@[ext]
structure subgraph :=
(adj' : V → V → Prop)
(adj_sub : ∀ ⦃v w : V⦄, adj' v w → G.adj v w)
(sym' : symmetric adj') -- i think we can also get rid of this

namespace simple_graph

/--
The Prop that states that `H` is a subgraph of `G`.
-/
def is_subgraph (H : simple_graph V) : Prop := ∀ ⦃v w : V⦄, H.adj v w → G.adj v w

variables (H : simple_graph V) (h : is_subgraph G H)

/--
If `G.is_subgraph H`, we can coerce `H` into the type `subgraph G`
-/
def to_subgraph : subgraph G :=
{ adj' := H.adj,
  adj_sub := h,
  sym' := H.sym }

end simple_graph

namespace subgraph

variable {G}

/--
The edges of `G'` consist of a subset of edges of `G`.
-/
def edge_set' (G' : subgraph G) : set (sym2 V) := sym2.from_rel G'.sym'

@[simp]
lemma mem_edge_set' {G' : subgraph G} {v w : V} : ⟦(v, w)⟧ ∈ edge_set' G' ↔ G'.adj' v w :=
by refl

lemma edge_sub (G' : subgraph G) : G'.edge_set' ⊆ G.edge_set :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w,
  simp only [mem_edge_set', mem_edge_set],
  apply G'.adj_sub,
end

lemma adj_symm' (G' : subgraph G) ⦃v w : V⦄ : G'.adj' v w ↔ G'.adj' w v :=
by { split; apply G'.sym' }

/--
Function lifting `G' : subgraph G` to `G' : simple_graph G.V`
-/
def to_simple_graph {G : simple_graph V} (G' : subgraph G) : simple_graph V :=
{ adj := G'.adj',
  sym := λ v w h, G'.sym' h,
  loopless := λ v h, --G.loopless v (G'.adj_sub h)
  begin
    exact G.loopless v (G'.adj_sub h)
  end }

/--
Coercion from `G' : subgraph G` to `G' : simple_graph G.V`
-/
def coe {V : Type*} {G : simple_graph V} (G' : subgraph G) : simple_graph V :=
{ adj := G'.adj',
  sym := G'.sym',
  loopless := λ v h, loopless G v (G'.adj_sub h) }

instance : inhabited (subgraph G) := { default :=
{ adj' := λ v w, false,
  adj_sub := λ v w, by finish,
  sym' := λ v w, by finish } }

end subgraph
#lint
