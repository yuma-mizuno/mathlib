import combinatorics.simple_graph.basic

universes u v z
variables {V : Type u} {W : Type v} {X : Type z}

namespace simple_graph

/--
A graph homomorphism is a map on vertex sets that respects the adjacency relations.
-/
abbreviation hom (G : simple_graph V) (G' : simple_graph W) : Type (max u v) :=
rel_hom (G.adj) (G'.adj)

infix ` →g ` : 50 := hom

namespace hom
variables {G : simple_graph V} {G' : simple_graph W} (f : G →g G')

lemma map_adj {v w : V} : G.adj v w → G'.adj (f v) (f w) :=
by apply f.map_rel'

def map_edge_set : G.edge_set → G'.edge_set :=
λ e, ⟨sym2.map f e.val, begin
  rcases e with ⟨e, h⟩,
  refine quotient.rec_on_subsingleton e (λ e h, _) h,
  rcases e with ⟨v, w⟩,
  rw sym2.map_pair_eq, rw mem_edge_set at ⊢ h,
  exact f.map_rel' h,
end⟩

def map_neighbor_set (v : V) : G.neighbor_set v → G'.neighbor_set (f v) :=
λ w, ⟨f w.val, begin
  rcases w with ⟨w, h⟩,
  rw mem_neighbor_set at h ⊢,
  exact map_adj f h,
end⟩

variables {G'' : simple_graph X}

/--
Composition of graph homomorphisms
-/
def comp (f' : G' →g G'') (f : G →g G') : G →g G'' :=
f'.comp f

@[simp] lemma comp_app (f' : G' →g G'') (f : G →g G') (v : V) : (f'.comp f) v = f' (f v) := rfl

@[simp] lemma coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f := rfl

class mono (f : G →g G') : Prop :=
(injective [] : function.injective f)

lemma mono_iff_injective (f : G →g G') : mono f ↔ function.injective f :=
⟨@mono.injective _ _ _ _ f, mono.mk⟩

instance mono.comp (f' : G' →g G'') (f : G →g G') [mono f'] [mono f] : mono (f'.comp f) :=
begin
  split, rw coe_comp,
  apply function.injective.comp (mono.injective f') (mono.injective f),
end

lemma map_neighbor_set.inj [mono f] (v : V) : function.injective (map_neighbor_set f v) :=
begin
  rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
  dsimp [map_neighbor_set] at h,
  rw subtype.mk_eq_mk at h ⊢,
  exact mono.injective f h,
end



end hom

end simple_graph
