/-
Copyright (c) 2021 Aaron Anderson, Jesse Michael Han, Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jesse Michael Han, Floris van Doorn
-/
import data.nat.basic
import logic.arity

/-!
# Basics on First-Order Structures
This file defines first-order languages and structures in the style of the
[Flypitch project](https://flypitch.github.io/).

## Main Definitions
* A `first_order.language` defines a language as a pair of functions from the natural numbers to
  `Type l`. One sends `n` to the type of `n`-ary functions, and the other sends `n` to the type of
  `n`-ary relations.
* A `first_order.language.Structure` interprets the symbols of a given `first_order.language` in the
  context of a given type.
* A `first_order.language.hom`, denoted `M →[L] N`, is a map from the `L`-structure `M` to the
  `L`-structure `N` that commutes with the interpretations of functions, and which preserves the
  interpretations of relations (although only in the forward direction).
* A `first_order.language.embedding`, denoted `M ↪[L] N`, is an embedding from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.
* A `first_order.language.equiv`, denoted `M ≃[L] N`, is an equivalence from the `L`-structure `M`
  to the `L`-structure `N` that commutes with the interpretations of functions, and which preserves
  the interpretations of relations in both directions.

## References
For the Flypitch project:
- [J. Han, F. van Doorn, *A formal proof of the independence of the continuum hypothesis*]
[flypitch_cpp]
- [J. Han, F. van Doorn, *A formalization of forcing and the unprovability of
the continuum hypothesis*][flypitch_itp]

-/

namespace first_order

/-- A first-order language consists of a type of functions of every natural-number arity and a
  type of relations of every natural-number arity. -/
structure language :=
(consts : Type*) (functions : ℕ → Type*) (relations : ℕ → Type*)

namespace language

/-- The empty language has no symbols. -/
def empty : language := ⟨pempty, λ _, pempty, λ _, pempty⟩

instance : inhabited language := ⟨empty⟩

variable (L : language)

/-- A language is relational when it has no function symbols. -/
class is_relational : Prop :=
(empty_consts : L.consts → false)
(empty_functions : ∀ n, L.functions n → false)

/-- A language is algebraic when it has no relation symbols. -/
class is_algebraic : Prop :=
(empty_relations : ∀ n, L.relations n → false)

variable {L}

instance is_relational_of_empty_functions {symb : ℕ → Type*} :
  is_relational ⟨pempty, λ _, pempty, symb⟩ :=
⟨pempty.elim, λ n, pempty.elim⟩

instance is_algebraic_of_empty_relations {csymb : Type*} {fsymb : ℕ → Type*} :
  is_algebraic ⟨csymb, fsymb, λ _, pempty⟩ :=
⟨λ n, pempty.elim⟩

instance is_relational_empty : is_relational (empty) := language.is_relational_of_empty_functions
instance is_algebraic_empty : is_algebraic (empty) := language.is_algebraic_of_empty_relations

variables (L) (M : Type*)

/-- A first-order structure on a type `M` consists of interpretations of all the symbols in a given
  language. Each function of arity `n` is interpreted as a function sending tuples of length `n`
  (modeled as `(fin n → M)`) to `M`, and a relation of arity `n` is a function from tuples of length
  `n` to `Prop`. -/
class Structure :=
(const_map : L.consts → M)
(fun_map : ∀{n}, L.functions n → ary_fun M M n)
(rel_map : ∀{n}, L.relations n → ary_rel M n)

variables (N : Type*) [L.Structure M] [L.Structure N]

open first_order.language.Structure

/-- A homomorphism between first-order structures is a function that commutes with the
  interpretations of functions and maps tuples in one structure where a given relation is true to
  tuples in the second structure where that relation is still true. -/
protected structure hom :=
(to_fun : M → N)
(map_const' : ∀ (c : L.consts), to_fun (const_map c) = const_map c . obviously)
(map_fun' : ∀{n} (f : L.functions n), (fun_map f).postcompose to_fun =
  (fun_map f).precompose to_fun . obviously)
(map_rel' : ∀{n} (r : L.relations n), (rel_map r) ≤ (rel_map r).precompose to_fun . obviously)

localized "notation A ` →[`:25 L `] ` B := L.hom A B" in first_order

/-- An embedding of first-order structures is an embedding that commutes with the
  interpretations of functions and relations. -/
protected structure embedding extends M ↪ N :=
(map_const' : ∀ (c : L.consts), to_fun (const_map c) = const_map c . obviously)
(map_fun' : ∀{n} (f : L.functions n), (fun_map f).postcompose to_fun =
  (fun_map f).precompose to_fun . obviously)
(map_rel' : ∀{n} (r : L.relations n), (rel_map r).precompose to_fun = (rel_map r) . obviously)

localized "notation A ` ↪[`:25 L `] ` B := L.embedding A B" in first_order

/-- An equivalence of first-order structures is an equivalence that commutes with the
  interpretations of functions and relations. -/
protected structure equiv extends M ≃ N :=
(map_const' : ∀ (c : L.consts), to_fun (const_map c) = const_map c . obviously)
(map_fun' : ∀{n} (f : L.functions n), (fun_map f).postcompose to_fun =
  (fun_map f).precompose to_fun . obviously)
(map_rel' : ∀{n} (r : L.relations n), (rel_map r).precompose to_fun = (rel_map r) . obviously)

localized "notation A ` ≃[`:25 L `] ` B := L.equiv A B" in first_order

variables {L M N} {P : Type*} [L.Structure P] {Q : Type*} [L.Structure Q]
namespace hom

@[simps] instance has_coe_to_fun : has_coe_to_fun (M →[L] N) :=
⟨(λ _, M → N), first_order.language.hom.to_fun⟩

@[simp] lemma to_fun_eq_coe {f : M →[L] N} : f.to_fun = (f : M → N) := rfl

lemma coe_injective : @function.injective (M →[L] N) (M → N) coe_fn
| f g h := by {cases f, cases g, cases h, refl}

@[ext]
lemma ext ⦃f g : M →[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M →[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

@[simp] lemma map_const (φ : M →[L] N) (c : L.consts) :
  φ (const_map c) = const_map c := φ.map_const' c

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) :
  (fun_map f).postcompose φ = (fun_map f).precompose φ := φ.map_fun' f

@[simp] lemma map_rel (φ : M →[L] N) {n : ℕ} (r : L.relations n) :
  (rel_map r) ≤ (rel_map r).precompose φ := φ.map_rel' r

variables (L) (M)
/-- The identity map from a structure to itself -/
@[refl] def id : M →[L] M :=
{ to_fun := id }

variables {L} {M}

instance : inhabited (M →[L] M) := ⟨id L M⟩

@[simp] lemma id_apply (x : M) :
  id L M x = x := rfl

/-- Composition of first-order homomorphisms -/
@[trans] def comp (hnp : N →[L] P) (hmn : M →[L] N) : M →[L] P :=
{ to_fun := hnp ∘ hmn,
  map_fun' := λ n f, begin
    rw [ary_fun.precompose_comp, ary_fun.postcompose_comp],
    simp [ary_fun.precompose_postcompose],
  end,
  map_rel' := λ n r, begin
    rw [ary_fun.precompose_comp],
    exact le_trans (hmn.map_rel r) (ary_rel.precompose_mono (hnp.map_rel r)),
  end }

@[simp] lemma comp_apply (g : N →[L] P) (f : M →[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M →[L] N) (g : N →[L] P) (h : P →[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end hom

namespace embedding

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ↪[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_const (φ : M ↪[L] N) (c : L.consts) :
  φ (const_map c) = const_map c := φ.map_const' c

@[simp] lemma map_fun (φ : M ↪[L] N) {n : ℕ} (f : L.functions n) :
  (fun_map f).postcompose φ = (fun_map f).precompose φ := φ.map_fun' f

@[simp] lemma map_rel (φ : M ↪[L] N) {n : ℕ} (r : L.relations n) :
  (rel_map r).precompose φ = rel_map r := φ.map_rel' r

/-- A first-order embedding is also a first-order homomorphism. -/
def to_hom (f : M ↪[L] N) : M →[L] N :=
{ to_fun := f }

@[simp]
lemma coe_to_hom {f : M ↪[L] N} : (f.to_hom : M → N) = f := rfl

lemma coe_injective : @function.injective (M ↪[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ↪[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ↪[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ↪[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity embedding from a structure to itself -/
@[refl] def refl : M ↪[L] M :=
{ to_fun := id,
  inj' := (function.embedding.refl _).injective }

variables {L} {M}

instance : inhabited (M ↪[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order embeddings -/
@[trans] def comp (hnp : N ↪[L] P) (hmn : M ↪[L] N) : M ↪[L] P :=
{ to_fun := hnp ∘ hmn,
  map_fun' := sorry,
  map_rel' := sorry,
  inj' := hnp.injective.comp hmn.injective }

@[simp] lemma comp_apply (g : N ↪[L] P) (f : M ↪[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order embeddings is associative. -/
lemma comp_assoc (f : M ↪[L] N) (g : N ↪[L] P) (h : P ↪[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end embedding

namespace equiv

/-- The inverse of a first-order equivalence is a first-order equivalence. -/
@[symm] def symm (f : M ≃[L] N) : N ≃[L] M :=
{ map_fun' := λ n f' x, begin
    simp only [equiv.to_fun_as_coe],
    rw [equiv.symm_apply_eq],
    refine eq.trans _ (f.map_fun' f' (f.to_equiv.symm ∘ x)).symm,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  map_rel' := λ n r x, begin
    simp only [equiv.to_fun_as_coe],
    refine (f.map_rel' r (f.to_equiv.symm ∘ x)).symm.trans _,
    rw [← function.comp.assoc, equiv.to_fun_as_coe, equiv.self_comp_symm, function.comp.left_id]
  end,
  .. f.to_equiv.symm }

@[simps] instance has_coe_to_fun : has_coe_to_fun (M ≃[L] N) :=
⟨(λ _, M → N), λ f, f.to_fun⟩

@[simp] lemma map_fun (φ : M →[L] N) {n : ℕ} (f : L.functions n) :
  (fun_map f).postcompose φ = (fun_map f).precompose φ := φ.map_fun' f

@[simp] lemma map_rel (φ : M ≃[L] N) {n : ℕ} (r : L.relations n) (x : fin n → M) :
  rel_map r (φ ∘ x) ↔ rel_map r x := φ.map_rel' r x

/-- A first-order equivalence is also a first-order embedding. -/
def to_embedding (f : M ≃[L] N) : M ↪[L] N :=
{ to_fun := f,
  inj' := f.to_equiv.injective }

/-- A first-order equivalence is also a first-order embedding. -/
def to_hom (f : M ≃[L] N) : M →[L] N :=
{ to_fun := f }

@[simp] lemma to_embedding_to_hom (f : M ≃[L] N) : f.to_embedding.to_hom = f.to_hom := rfl

@[simp]
lemma coe_to_hom {f : M ≃[L] N} : (f.to_hom : M → N) = (f : M → N) := rfl

@[simp] lemma coe_to_embedding (f : M ≃[L] N) : (f.to_embedding : M → N) = (f : M → N) := rfl

lemma coe_injective : @function.injective (M ≃[L] N) (M → N) coe_fn
| f g h :=
begin
  cases f,
  cases g,
  simp only,
  ext x,
  exact function.funext_iff.1 h x,
end

@[ext]
lemma ext ⦃f g : M ≃[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
coe_injective (funext h)

lemma ext_iff {f g : M ≃[L] N} : f = g ↔ ∀ x, f x = g x :=
⟨λ h x, h ▸ rfl, λ h, ext h⟩

lemma injective (f : M ≃[L] N) : function.injective f := f.to_embedding.injective

variables (L) (M)
/-- The identity equivalence from a structure to itself -/
@[refl] def refl : M ≃[L] M :=
{ to_equiv := equiv.refl M }

variables {L} {M}

instance : inhabited (M ≃[L] M) := ⟨refl L M⟩

@[simp] lemma refl_apply (x : M) :
  refl L M x = x := rfl

/-- Composition of first-order equivalences -/
@[trans] def comp (hnp : N ≃[L] P) (hmn : M ≃[L] N) : M ≃[L] P :=
{ to_fun := hnp ∘ hmn,
  .. (hmn.to_equiv.trans hnp.to_equiv) }

@[simp] lemma comp_apply (g : N ≃[L] P) (f : M ≃[L] N) (x : M) :
  g.comp f x = g (f x) := rfl

/-- Composition of first-order homomorphisms is associative. -/
lemma comp_assoc (f : M ≃[L] N) (g : N ≃[L] P) (h : P ≃[L] Q) :
  (h.comp g).comp f = h.comp (g.comp f) := rfl

end equiv

end language
end first_order
