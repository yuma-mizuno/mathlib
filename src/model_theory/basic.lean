import data.nat.basic
import algebra.group.defs
import data.fintype.basic

universe u

variables {α : Type u} {β : Type u}

--move to fin
namespace fin

def sum_uncurry {m n : ℕ} (x : fin m → α) (y : fin n → α) (i : fin (m + n)) : α := sorry
--ite (i < ↑m) (x ↑(↑i : ℕ)) (y ↑(↑i - m))

def set.prod {m n : ℕ} (s : set (fin m → α)) (t : set (fin n → α)) : set (fin (m + n) → α) :=
{ z | ∃ (x: fin m → α) (y : fin n → α), x ∈ s ∧ y ∈ t ∧ z = fin.sum_uncurry x y }

end fin

--move to bounded_lattice
protected def subtype.bounded_lattice [bounded_lattice α] {P : α → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
  (Pinf : ∀{{x y}}, P x → P y → P (x ⊓ y)) (Psup : ∀{{x y}}, P x → P y → P (x ⊔ y)) :
  bounded_lattice {x : α // P x} :=
{ top := ⟨⊤, Ptop⟩,
  le_top := λ x, @le_top α _ x,
..subtype.semilattice_inf_bot Pbot Pinf, ..subtype.semilattice_sup Psup }

--move to set.basic
@[simp]
theorem set.top_eq_univ : (⊤ : set α) = set.univ := rfl

open fin

structure Language : Type (u+1) :=
(functions : ℕ → Type u) (relations : ℕ → Type u)

def Language.constants (L : Language) := L.functions 0

def empty_symbols : ℕ → Type u := λ _, pempty

variable (L : Language.{u})

def Language.relational : Prop := ∀ n, L.functions n → false

def Language.algebraic : Prop := ∀ n, L.relations n → false

variable {L}

def Language.relational_of_empty {symb : ℕ → Type u}  : Language.relational ⟨empty_symbols, symb⟩ :=
by { intro n, apply pempty.elim }

def Language.algebraic_of_empty {symb : ℕ → Type u}  : Language.algebraic ⟨symb, empty_symbols⟩ :=
by { intro n, apply pempty.elim }

variable (L)

structure Structure  :=
(carrier : Type u)
(fun_map : ∀{n}, L.functions n → (fin n → carrier) → carrier)
(rel_map : ∀{n}, L.relations n → (fin n → carrier) → Prop)

variable {L}

instance has_coe_Structure : has_coe_to_sort (Structure L) :=
⟨Type u, Structure.carrier⟩

variable (M : Structure L)

structure substructure :=
(carrier : set M)
(fun_mem : ∀{n}, ∀ (f : L.functions n) (x : fin n → M),
  (∀ (i : fin n), x i ∈ carrier) → M.fun_map f x ∈ carrier)

variable {M}

def substructure_of_relational (rel : L.relational) (s : set M) : substructure M :=
⟨s, by { intros n f x h, exfalso, apply rel n f }⟩

inductive definable_params (params : set M) : Π n : ℕ, set (fin n → M) → Prop
| param {a : M} : a ∈ params → definable_params 1 {λ i : fin 1, a}
| univ (n : ℕ) : definable_params n set.univ
| eq (n : ℕ) (i j : fin n) : definable_params n {x | x i = x j}
| times {n : ℕ} {s : set (fin n → M)} :
  definable_params n s → definable_params (n + 1) {x | tail x ∈ s}
| compl {n : ℕ} {s : set (fin n → M)} : definable_params n s → definable_params n s.compl
| inter {n : ℕ} {s t : set (fin n → M)} :
  definable_params n s → definable_params n t → definable_params n (s ∩ t)
| union {n : ℕ} {s t : set (fin n → M)} :
  definable_params n s → definable_params n t → definable_params n (s ∪ t)
| prod {m n : ℕ} {s : set (fin m → M)} {t : set (fin n → M)} :
  definable_params m s → definable_params n t → definable_params (m + n) (fin.set.prod s t)
| func {n : ℕ} {f : L.functions n} : definable_params (n + 1) {x | x 0 = M.fun_map f (tail x) }
| rel {n : ℕ} {f : L.relations n} : definable_params n {x | M.rel_map f x }
| proj {n : ℕ} {s : set (fin (n + 1) → M)} :
  definable_params (n + 1) s → definable_params n {x | ∃ y ∈ s, x = tail y}

namespace definable_params
variables (params : set M) (n : ℕ)

def empty : definable_params params n ∅ :=
by { rw ← set.compl_univ, apply definable_params.compl, apply definable_params.univ }

def bot : definable_params params n ⊥ :=
by {apply definable_params.empty}

def top : definable_params params n ⊤ :=
by {apply definable_params.univ}

variables {s t : set (fin n → M)}

def inf : definable_params params n s → definable_params params n t →
  definable_params params n (s ⊓ t) :=
by { rw set.inf_eq_inter, apply definable_params.inter, }

def sup : definable_params params n s → definable_params params n t →
  definable_params params n (s ⊔ t) :=
by { rw set.sup_eq_union, apply definable_params.union, }

end definable_params

variable (M)

def definable := definable_params (set.univ : set M)

variable (n : ℕ)

def definable_set := {s : set (fin n → M) // definable M n s}

instance : bounded_lattice (definable_set M n) :=
begin
  apply subtype.bounded_lattice; unfold definable,
  apply definable_params.bot,
  apply definable_params.top,
  apply definable_params.inf,
  apply definable_params.sup,
end

section maps

variables {n} {M} (L) (M) (N : Structure L)

structure first_order_map :=
(to_fun : M → N)
(map_fun : ∀{n}, ∀ f : L.functions n, to_fun ∘ M.fun_map f = N.fun_map f ∘ (function.comp to_fun))
(map_rel : ∀{n}, ∀ (r : L.relations n) (x : fin n → M),
  M.rel_map r x → N.rel_map r (function.comp to_fun x))

notation A ` →[`:25 L `] ` B := first_order_map L A B

structure first_order_embedding extends M ↪ N :=
(map_fun : ∀{n}, ∀ f : L.functions n,
  to_embedding ∘ M.fun_map f = N.fun_map f ∘ (function.comp to_embedding))
(map_rel : ∀{n}, ∀ (r : L.relations n), M.rel_map r = N.rel_map r ∘ (function.comp to_embedding))

notation A ` ↪[`:25 L `] ` B := first_order_embedding L A B

structure first_order_equiv extends M ≃ N :=
(map_fun : ∀{n}, ∀ f : L.functions n, to_fun ∘ M.fun_map f = N.fun_map f ∘ (function.comp to_fun))
(map_rel : ∀{n}, ∀ (r : L.relations n), M.rel_map r = N.rel_map r ∘ (function.comp to_fun))

notation A ` ≃[`:25 L `] ` B := first_order_equiv L A B

-- needs formulas
structure elementary_embedding extends M ↪[L] N := sorry

notation A ` ↪ₑ[`:25 L `] ` B := elementary_embedding L A B

-- needs formulas
structure elementary_equiv extends M ≃[L] N := sorry

notation A ` ≃ₑ[`:25 L `] ` B := elementary_equiv L A B

end maps
