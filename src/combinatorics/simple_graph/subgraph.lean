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
Note: subgraphs could also have been defined as in `subgraph.of_edge_set'`.  We prove this alternative definition is equivalent.
-/
@[ext]
structure subgraph :=
(V' : set V)
(adj' : V → V → Prop)
(adj_sub : ∀ ⦃v w : V⦄, adj' v w → G.adj v w)
(edge_vert : ∀ ⦃v w : V⦄, adj' v w → v ∈ V')
(sym' : symmetric adj')

namespace subgraph

variable {G}

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

lemma has_verts (G' : subgraph G) : ∀ ⦃e : sym2 V⦄ ⦃v : V⦄, e ∈ G'.edge_set' → v ∈ e → v ∈ G'.V' :=
begin
  intro e,
  refine quotient.rec_on_subsingleton e (λ e, _),
  cases e with v w, intros u he hu,
  simp only [mem_edge_set'] at he,
  cases sym2.mem_iff.mp hu; subst u,
  exact G'.edge_vert he,
  exact G'.edge_vert (G'.sym' he),
end

lemma adj_symm' (G' : subgraph G) ⦃v w : V⦄ : G'.adj' v w ↔ G'.adj' w v :=
by { split; apply G'.sym' }

def to_simple_graph {G : simple_graph V} (G' : subgraph G) : simple_graph G'.V' :=
{ adj := λ v w, G'.adj' ↑v ↑w,
  sym := λ v w h, G'.sym' h,
  loopless := λ ⟨v, _⟩ h, loopless G v (G'.adj_sub h) }

def subgraph.coe {V : Type*} {G : simple_graph V} (G' : subgraph G) : simple_graph V :=
{ adj := G'.adj',
  sym := G'.sym',
  loopless := λ v h, loopless G v (G'.adj_sub h) }

end subgraph
