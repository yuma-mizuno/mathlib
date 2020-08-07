import model_theory.basic

universe u

open set

variables {L : Language.{u}} {μ : Type u} (M : Structure L μ)

namespace Structure

variables {n : ℕ} (f : L.functions n) (s : set μ)

def closed_under : Prop :=
∀ (x : fin n → μ), (∀ (i : fin n), x i ∈ s) → M.fun_map f x ∈ s

variables {f} {s} {t : set μ}

lemma closed_under_inter (hs : M.closed_under f s) (ht : M.closed_under f t) :
  M.closed_under f (s ∩ t) :=
λ x h, mem_inter (hs x (λ i, mem_of_mem_inter_left (h i))) (ht x (λ i, mem_of_mem_inter_right (h i)))

lemma closed_under_inf (hs : M.closed_under f s) (ht : M.closed_under f t) :
  M.closed_under f (s ⊓ t) := closed_under_inter M hs ht

variables {S : set (set μ)}

lemma closed_under_Inf (hS : ∀ s, s ∈ S → M.closed_under f s) : M.closed_under f (Inf S) :=
λ x h s hs, hS s hs x (λ i, h i s hs)

end Structure

structure substructure :=
(carrier : set μ)
(fun_mem : ∀{n}, ∀ (f : L.functions n), M.closed_under f carrier)

variable {M}

instance : has_coe (substructure M) (set μ) := { coe := substructure.carrier }

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

@[simp]
lemma closed_under (s : substructure M) {n : ℕ} (f : L.functions n) :
  M.closed_under f ↑s := s.fun_mem f

instance : has_mem μ (substructure M) := ⟨λ m s, m ∈ (s : set μ)⟩

/- Two substructures are equal if the underlying set are the same. -/
theorem ext' {s t : substructure M} (h : (s : set μ) = t) : s = t :=
by { cases s, cases t, congr, exact h }

/- Two substructures are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {s t : substructure M} :
  s = t ↔ (s : set μ) = t := ⟨λ h, h ▸ rfl, ext'⟩

/-- Two substructures are equal if they have the same elements. -/
@[ext]
theorem ext {s t : substructure M}
  (h : ∀ x : μ, x ∈ s ↔ x ∈ t) : s = t := ext' $ set.ext h

instance : has_le (substructure M) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩

lemma le_def {s t : substructure M} : s ≤ t ↔ ∀ ⦃x : μ⦄, x ∈ s → x ∈ t := iff.rfl

@[simp]
lemma coe_le_coe {s t : substructure M} : (s : set μ) ≤ t ↔ s ≤ t := iff.rfl

@[simp]
lemma coe_subset_coe {s t : substructure M} : (s : set μ) ⊆ t ↔ s ≤ t := iff.rfl

instance : partial_order (substructure M) :=
{ le := (≤),
  .. partial_order.lift (coe : substructure M → set μ) (λ a b, ext') }

@[simp, norm_cast]
lemma mem_coe {s : substructure M} {a : μ} : a ∈ (s : set μ) ↔ a ∈ s := iff.rfl

@[simp, norm_cast]
lemma coe_coe (s : substructure M) : ↥(s : set μ) = s := rfl

end substructure

protected lemma substructure.exists {s : substructure M} {p : s → Prop} :
  (∃ x : s, p x) ↔ ∃ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.exists

protected lemma substructure.forall {s : substructure M} {p : s → Prop} :
  (∀ x : s, p x) ↔ ∀ x ∈ s, p ⟨x, ‹x ∈ s›⟩ :=
set_coe.forall

open substructure

section substructure

instance : has_inf (substructure M) :=
{ inf := λ s t, ⟨↑s ⊓ ↑t, λ n f, M.closed_under_inf (s.fun_mem f) (t.fun_mem f)⟩ }

@[simp] lemma coe_inf (s t : substructure M) : (↑(s ⊓ t) : set μ) = (s : set μ) ⊓ t := rfl

instance : semilattice_inf (substructure M) :=
{ le_inf := λ a b c, begin
    repeat {rw ← substructure.coe_le_coe},
    rw coe_inf, intros h1 h2,
    apply le_inf h1 h2,
  end,
  inf_le_left := λ a b c, begin
    rw [← mem_coe, coe_inf, inf_eq_inter, mem_inter_iff], intro h, apply h.left,
  end,
  inf_le_right := λ a b c, begin
    rw [← substructure.mem_coe, coe_inf, inf_eq_inter, mem_inter_iff], intro h, apply h.right,
  end,
..substructure.partial_order, .. substructure.has_inf, }

instance : has_Inf (substructure M) :=
{ Inf := λ S, ⟨Inf (coe '' S), λ n f, M.closed_under_Inf (λ s hs, by {
  cases hs with st hst, rw ← hst.2, apply st.closed_under,
})⟩ }

@[simp] lemma coe_Inf (S : set (substructure M)) : (↑(Inf S) : set μ) = Inf (coe '' S) := rfl

/-- The `substructure` consisting of the entire `Structure`. -/
instance : has_top (substructure M) := ⟨⟨univ, λ n f x hx, mem_univ _⟩⟩

@[simp] lemma mem_top (x : μ) : x ∈ (⊤ : substructure M) := mem_univ x

@[simp] lemma coe_top : ((⊤ : substructure M) : set μ) = set.univ := rfl

/-- `substructure`s of a first-order `Structure` form a `complete_lattice`. -/
instance : complete_lattice (substructure M) :=
{ top          := (⊤),
  le_top       := λ S x hx, mem_top x,inf := (⊓),
  le_inf       := λ a b c ha hb x hx, ⟨ha hx, hb hx⟩,
  inf_le_left  := λ a b x, and.left,
  inf_le_right := λ a b x, and.right,
  .. complete_lattice_of_Inf (substructure M)
    (λ S, is_glb.of_image (@substructure.coe_le_coe _ _ _) (is_glb_Inf _)) }

variables (M) (s : set μ)

/-- The `substructure` generated by a `set`. -/
def closure : substructure M := Inf {t | s ⊆ t}

variables {M} {s} {S : substructure M}

/-- The `substructure` generated by a `set` includes the `set`. -/
@[simp] lemma subset_closure : s ⊆ closure M s :=
by { intros x hx t ht, cases ht, rw ← ht_h.2, apply ht_h.1 hx, }

/-- A `substructure` includes `closure M s` if and only if it includes `s`. -/
@[simp] lemma closure_le : closure M s ≤ S ↔ s ⊆ S :=
⟨subset.trans subset_closure, λ h, Inf_le h⟩

lemma bot_eq_closure_empty : ⊥ = closure M ∅ :=
le_antisymm (le_Inf (λ b hb, bot_le)) (Inf_le (empty_subset ↑⊥))

lemma closure_mono ⦃s t : set μ⦄ (h : s ⊆ t) : closure M s ≤ closure M t :=
closure_le.2 $ subset.trans h subset_closure

lemma closure_eq_of_le (h₁ : s ⊆ S) (h₂ : S ≤ closure M s) : closure M s = S :=
le_antisymm (closure_le.2 h₁) h₂

variable (S)

/-- An induction principle for closure membership. If `p` holds for all elements of `s`, and
is preserved under function application, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_eliminator] lemma closure_induction {p : μ → Prop} {x} (h : x ∈ closure M s)
  (Hs : ∀ x ∈ s, p x) (Hfun : ∀ (n : ℕ) (f : L.functions n), M.closed_under f p) : p x :=
(@closure_le _ _ _ _ ⟨p, Hfun⟩).2 Hs h

/-- If `s` is a dense set in a structure `M` on `μ`, `substructure.closure M s = ⊤`, then in order to prove that
some predicate `p` holds for all `x : μ` it suffices to verify `p x` for `x ∈ s`, verify `p 1`,
and verify that `p x` and `p y` imply `p (x * y)`. -/
@[elab_as_eliminator]
lemma dense_induction {p : μ → Prop} (x : μ) {s : set μ} (hs : closure M s = ⊤) (Hs : ∀ x ∈ s, p x)
  (Hfun : ∀ (n : ℕ) (f : L.functions n), M.closed_under f p) : p x :=
have ∀ x ∈ closure M s, p x, from λ x hx, closure_induction hx Hs Hfun,
by simpa [hs] using this x

variable (M)

/-- `closure` forms a Galois insertion with the coercion to set. -/
protected def gi : galois_insertion (closure M) coe :=
{ choice := λ s _, closure M s,
  gc := λ s t, closure_le,
  le_l_u := λ s, subset_closure,
  choice_eq := λ s h, rfl }

/-- Closure of a substructure `S` equals `S`. -/
@[simp] lemma closure_eq : closure M (S : set μ) = S := (gi M).l_u_eq S

@[simp] lemma closure_empty : closure M ∅ = ⊥ :=
(gi M).gc.l_bot

@[simp] lemma closure_univ : closure M univ = ⊤ := le_antisymm le_top subset_closure

lemma closure_union (s t : set μ) : closure M (s ∪ t) = closure M s ⊔ closure M t :=
(gi M).gc.l_sup

lemma closure_Union {ι} (s : ι → set μ) : closure M (⋃ i, s i) = ⨆ i, closure M (s i) :=
(gi M).gc.l_supr

@[simp] lemma closure_eq_of_relational (rel : L.relational) :
  closure M s = substructure.of_relational rel s :=
closure_eq_of_le (subset.refl _) subset_closure

end substructure

namespace first_order_hom

variables {M} {ν : Type u} {π : Type u} {N : Structure L ν} {P : Structure L π} (S : substructure M)

open substructure

/-- The substructure of elements `x : M` such that `f x = g x` -/
def eq_mlocus (f g : M →[L] N) : substructure M :=
{ carrier := {x : μ | f x = g x},
  fun_mem := λ n fn x hx, by { dsimp,
    transitivity (f.to_fun ∘ M.fun_map fn) x, rw function.comp_apply, refl,
    transitivity (g.to_fun ∘ M.fun_map fn) x, swap,  rw function.comp_apply, refl,
    rw map_fun f fn, rw map_fun g fn, repeat {rw function.comp_apply},
    have h : f.to_fun ∘ x = g.to_fun ∘ x,
    { ext, repeat {rw function.comp_apply},
      change ∀ i, f.to_fun (x i) = g.to_fun (x i) at hx,
      rw hx x_1, },
    rw h, } }

/-- If two `first_order_hom`s are equal on a set, then they are equal on its substructure closure. -/
lemma eq_on_mclosure {f g : M →[L] N} {s : set μ} (h : set.eq_on f g s) :
  set.eq_on f g (closure M s) :=
show closure M s ≤ f.eq_mlocus g, from closure_le.2 h

lemma eq_of_eq_on_mtop {f g : M →[L] N} (h : set.eq_on f g (⊤ : substructure M)) :
  f = g :=
ext $ λ x, h trivial

variable {s : set μ}

lemma eq_of_eq_on_mdense (hs : closure M s = ⊤) {f g : M →[L] N} (h : s.eq_on f g) :
  f = g :=
eq_of_eq_on_mtop $ hs ▸ eq_on_mclosure h

end first_order_hom
