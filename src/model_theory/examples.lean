import model_theory.basic

universe u

open Language

inductive L_add_group_fun : ℕ → Type u
| zero    : L_add_group_fun 0
| plus    : L_add_group_fun 2

inductive L_ring_fun : ℕ → Type u
| zero    : L_ring_fun 0
| one     : L_ring_fun 0
| plus    : L_ring_fun 2
| times   : L_ring_fun 2

inductive L_le_rel : ℕ → Type u
| le      : L_le_rel 2

def L_add_group : Language.{u} := ⟨L_add_group_fun, empty_symbols⟩

lemma algebraic_L_add_group : L_add_group.algebraic := algebraic_of_empty

def L_ring : Language.{u} := ⟨L_ring_fun, empty_symbols⟩

lemma algebraic_L_ring : L_add_group.algebraic := algebraic_of_empty

def L_le : Language.{u} := ⟨empty_symbols, L_ring_fun⟩

lemma relational_L_le : L_le.relational := relational_of_empty

def L_ordered_add_group : Language.{u} := ⟨L_add_group_fun, L_le_rel⟩

variables {L : Language.{u}} {M : Structure L} [partial_order M]
variables {le_symb : L.relations 2}
variables (le_symb_is_le : ∀ x : fin 2 → M, M.rel_map le_symb x = (x 0 ≤ x 1))

def o_minimal : Prop :=
∀ (s : definable_set M 1), ∃ (sings : finset M) (ends : finset (M × M)),
  set.image (λ i : fin 1 → M, i 0) s.val =
  ↑sings ∪ ⋃ (x : M × M) (h : x ∈ ends), set.Ioo x.fst x.snd
