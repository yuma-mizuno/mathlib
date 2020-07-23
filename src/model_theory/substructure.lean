import model_theory.basic

universe u

variables {L : Language.{u}} {μ : Type u} (M : Structure L μ)

structure substructure :=
(carrier : set μ)
(fun_mem : ∀{n}, ∀ (f : L.functions n) (x : fin n → μ),
  (∀ (i : fin n), x i ∈ carrier) → M.fun_map f x ∈ carrier)

variable {M}

instance : has_coe (substructure M) (set M) := { coe := substructure.carrier }

instance : has_coe_to_sort (substructure M) := ⟨_, λ s, ↥s⟩

def subtype.to_Structure {P : μ → Prop} (Pfun : ∀{n}, ∀ (f : L.functions n) (x : fin n → μ),
  (∀ (i : fin n), P (x i)) → P (M.fun_map f x)) : Structure L {x // P x} :=
{ fun_map := λ n f a, ⟨M.fun_map f ↑a, Pfun f ↑a (λ i, (a i).property)⟩,
  rel_map := λ n r a, M.rel_map r ↑a, }

namespace substructure
def to_Structure (s : substructure M) : Structure L ↥s :=
subtype.to_Structure s.fun_mem

def of_relational (rel : L.relational) (s : set μ) : substructure M :=
⟨s, by { intros n f x h, exfalso, apply rel n f }⟩

instance : has_mem μ (substructure M) := ⟨λ m s, m ∈ (s : set M)⟩

/- Two substructures are equal if the underlying set are the same. -/
theorem ext' {s t : substructure M} (h : (s : set μ) = t) : s = t :=
by { cases s, cases t, congr, exact h }

/- Two substructures are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : substructure M} :
  s = t ↔ (s : set μ) = t := ⟨λ h, h ▸ rfl, ext'⟩

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {s t : substructure M}
  (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := ext' $ set.ext h

instance : has_le (substructure M) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

lemma le_def {s t : substructure M} : s ≤ t ↔ ∀ ⦃x : μ⦄, x ∈ s → x ∈ t := iff.rfl

@[simp]
lemma coe_subset_coe {s t : substructure M} : (s : set μ) ⊆ t ↔ s ≤ t := iff.rfl

instance : partial_order (substructure M) :=
{ le := (≤),
  .. partial_order.lift (coe : substructure M → set μ) (λ a b, ext') }

@[simp, norm_cast]
lemma mem_coe {s : substructure M} {a : M} : a ∈ (s : set M) ↔ a ∈ s := iff.rfl

@[simp, norm_cast]
lemma coe_coe (s : substructure M) : ↥(s : set M) = s := rfl

end substructure

protected lemma substructure.exists {s : substructure M} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma substructure.forall {s : substructure M} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

section substructure

instance : complete_lattice (substructure M) :=
{ le := (≤),
  sup := λ M1 M2, ⟨M1.carrier ⊔ M2.carrier, begin
  simp only [set.sup_eq_union, set.mem_union_eq],
  end ⟩,
  inf := sorry,

}


end substructure
