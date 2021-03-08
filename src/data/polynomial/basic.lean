/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import tactic.ring_exp
import tactic.chain
import algebra.monoid_algebra
import data.finset.sort

/-!
# Theory of univariate polynomials

Polynomials are represented as `monoid_algebra R (multiplicative ℕ)`,
where `R` is a commutative semiring.
In this file, we define `polynomial`, provide basic instances, and prove an `ext` lemma.
-/

noncomputable theory

/-- `polynomial R` is the type of univariate polynomials over `R`.

Polynomials should be seen as (semi-)rings with the additional constructor `X`.
The embedding from `R` is called `C`. -/
def polynomial (R : Type*) [semiring R] :=
monoid_algebra R (multiplicative ℕ)

open finsupp monoid_algebra multiplicative
open_locale big_operators

namespace polynomial
universes u
variables {R : Type u} {a : R} {m n : ℕ}

section semiring
variables [semiring R] {p q : polynomial R}

instance : inhabited (polynomial R) := monoid_algebra.inhabited _ _
instance : semiring (polynomial R) := monoid_algebra.semiring
instance {S} [semiring S] [semimodule S R] : semimodule S (polynomial R) :=
monoid_algebra.semimodule

instance [subsingleton R] : unique (polynomial R) := monoid_algebra.unique

/--
Powers of non-zero coefficients.
-/
def support (p : polynomial R) : finset ℕ :=
p.support.map to_add.to_embedding

@[simp] lemma support_zero : (0 : polynomial R).support = ∅ := rfl

@[simp] lemma support_eq_empty : p.support = ∅ ↔ p = 0 :=
by simp [support]

lemma card_support_eq_zero : p.support.card = 0 ↔ p = 0 :=
by simp

/--
Sum over the non-zero coefficients of a polynomial.
-/
def sum {S} [add_comm_monoid S] (p : polynomial R) (f : ℕ → R → S) : S :=
p.sum (λ n, f n.to_add)

/--
Replaces the coefficient of X^n by zero.
-/
def erase (p : polynomial R) (n : ℕ) : polynomial R :=
p.erase (of_add n)

@[simp] lemma erase_support {p : polynomial R} {n : ℕ} :
  (p.erase n).support = p.support.erase n :=
by { ext, simp [erase, support] }

/-- `monomial s a` is the monomial `a * X^s` -/
def monomial (n : ℕ) : R →ₗ[R] polynomial R := finsupp.lsingle (of_add n)

@[simp] lemma monomial_zero_right (n : ℕ) :
  monomial n (0 : R) = 0 :=
finsupp.single_zero

lemma monomial_support [decidable_eq R] (n : ℕ) (r : R) :
  (monomial n r).support = if r = 0 then ∅ else {n} :=
if h : r = 0 then
  by simp [h]
else
  begin
    rw [support, support_single_ne_zero h] {md := tactic.transparency.semireducible},
    simp [h]
  end

lemma monomial_add (n : ℕ) (r s : R) :
  monomial n (r + s) = monomial n r + monomial n s :=
finsupp.single_add

lemma monomial_mul_monomial (n m : ℕ) (r s : R) :
  monomial n r * monomial m s = monomial (n + m) (r * s) :=
monoid_algebra.single_mul_single

lemma smul_monomial {S} [semiring S] [semimodule S R] (a : S) (n : ℕ) (b : R) :
  a • monomial n b = monomial n (a • b) :=
finsupp.smul_single _ _ _

lemma support_add : (p + q).support ⊆ p.support ∪ q.support :=
have to_add.to_embedding.trans of_add.to_embedding = function.embedding.refl (multiplicative ℕ),
  by { ext, simp },
begin
  rw ← @finset.map_subset_map _ _ of_add.to_embedding,
  simp only [support, finset.map_map, finset.map_union, this, finset.map_refl],
  convert @support_add _ _ _ p q
end

/-- `X` is the polynomial variable (aka indeterminant). -/
def X : polynomial R := monomial 1 1

/-- `X` commutes with everything, even when the coefficients are noncommutative. -/
lemma X_mul : X * p = p * X :=
by { ext, simp [X, monomial, monoid_algebra.mul_apply, sum_single_index, mul_comm] }

lemma X_pow_mul {n : ℕ} : X^n * p = p * X^n :=
begin
  induction n with n ih,
  { simp, },
  { conv_lhs { rw pow_succ', },
    rw [mul_assoc, X_mul, ←mul_assoc, ih, mul_assoc, ←pow_succ'], }
end

lemma X_pow_mul_assoc {n : ℕ} : (p * X^n) * q = (p * q) * X^n :=
by rw [mul_assoc, X_pow_mul, ←mul_assoc]

lemma commute_X (p : polynomial R) : commute X p := X_mul

/-- coeff p n is the coefficient of X^n in p -/
def coeff (p : polynomial R) (n : ℕ) : R :=
@coe_fn (multiplicative ℕ →₀ R) finsupp.has_coe_to_fun p (of_add n)

@[simp] lemma coeff_mk (s) (f) (h) : coeff (finsupp.mk s f h : polynomial R) = f ∘ of_add := rfl

lemma coeff_monomial : coeff (monomial n a) m = if n = m then a else 0 :=
by { dsimp [monomial, coeff], rw finsupp.single_apply, simp }

@[simp] lemma coeff_zero (n : ℕ) : coeff (0 : polynomial R) n = 0 := rfl

@[simp] lemma coeff_one_zero : coeff (1 : polynomial R) 0 = 1 := coeff_monomial

@[simp] lemma coeff_X_one : coeff (X : polynomial R) 1 = 1 := coeff_monomial

@[simp] lemma coeff_X_zero : coeff (X : polynomial R) 0 = 0 := coeff_monomial

@[simp] lemma coeff_monomial_succ : coeff (monomial (n+1) a) 0 = 0 :=
by simp [coeff_monomial]

@[simp] lemma coeff_monomial_same : coeff (monomial n a) n = a :=
by simp [coeff_monomial]

lemma coeff_X : coeff (X : polynomial R) n = if 1 = n then 1 else 0 := coeff_monomial

lemma coeff_X_of_ne_one {n : ℕ} (hn : n ≠ 1) : coeff (X : polynomial R) n = 0 :=
by rw [coeff_X, if_neg hn.symm]

lemma coeff_erase {i n : ℕ} : (p.erase i).coeff n = if n = i then 0 else p.coeff n :=
by simp [erase, coeff, finsupp.erase]

@[simp] lemma coeff_erase_same {i : ℕ} : (p.erase i).coeff i = 0 :=
by simp [coeff_erase]

theorem ext_iff {p q : polynomial R} : p = q ↔ ∀ n, coeff p n = coeff q n :=
by simp [finsupp.ext_iff, coeff, forall_multiplicative_iff]

@[ext] lemma ext {p q : polynomial R} : (∀ n, coeff p n = coeff q n) → p = q :=
ext_iff.2

@[ext] lemma add_hom_ext' {M : Type*} [add_monoid M] {f g : polynomial R →+ M}
  (h : ∀ n, f.comp (monomial n).to_add_monoid_hom = g.comp (monomial n).to_add_monoid_hom) :
  f = g :=
finsupp.add_hom_ext' (λ x, by simpa [monomial] using h (to_add x))

lemma add_hom_ext {M : Type*} [add_monoid M] {f g : polynomial R →+ M}
  (h : ∀ n a, f (monomial n a) = g (monomial n a)) :
  f = g :=
finsupp.add_hom_ext (λ x, by simpa [monomial] using h (to_add x))

@[ext] lemma lhom_ext' {M : Type*} [add_comm_monoid M] [semimodule R M] {f g : polynomial R →ₗ[R] M}
  (h : ∀ n, f.comp (monomial n) = g.comp (monomial n)) :
  f = g :=
finsupp.lhom_ext' (λ x, by simpa [monomial] using h (to_add x))

-- this has the same content as the subsingleton
lemma eq_zero_of_eq_zero (h : (0 : R) = (1 : R)) (p : polynomial R) : p = 0 :=
by rw [←one_smul R p, ←h, zero_smul]

lemma support_monomial (n) (a : R) (H : a ≠ 0) : (monomial n a).support = singleton n :=
by simp [support, monomial, finsupp.support_single_ne_zero H]

lemma support_monomial' (n) (a : R) : (monomial n a).support ⊆ singleton n :=
begin
  refine set.subset.trans (finset.map_subset_map.2 _) _,
  swap,
  apply finsupp.support_single_subset,
  simp,
end

lemma X_pow_eq_monomial (n) : X ^ n = monomial n (1:R) :=
begin
  induction n with n hn,
  { refl, },
  { rw [pow_succ', hn, X, monomial_mul_monomial, one_mul] },
end

lemma support_X_pow (H : ¬ (1:R) = 0) (n : ℕ) : (X^n : polynomial R).support = singleton n :=
begin
  convert support_monomial n 1 H,
  exact X_pow_eq_monomial n,
end

lemma support_X_empty (H : (1:R)=0) : (X : polynomial R).support = ∅ :=
by simpa [X, support, monomial]

lemma support_X (H : ¬ (1 : R) = 0) : (X : polynomial R).support = singleton 1 :=
begin
  rw [← pow_one X, support_X_pow H 1],
end

lemma monomial_left_inj {R : Type*} [semiring R] {a : R} (ha : a ≠ 0) {i j : ℕ} :
  monomial i a = monomial j a ↔ i = j :=
begin
  simp only [monomial, lsingle_apply],
  rw finsupp.single_left_inj,
  simp,
  assumption
end

section sum

variables {S : Type*} [add_comm_monoid S] {f : ℕ → R → S}

lemma sum_def : p.sum f = ∑ n in p.support, f n (p.coeff n) :=
by simp [sum, support, finsupp.sum, coeff]

@[simp] lemma zero_sum : (0 : polynomial R).sum f = 0 :=
by simp [sum]

lemma monomial_sum [decidable_eq R] :
  (monomial n a).sum f = if a = 0 then 0 else f n a :=
begin
  simp only [sum_def, monomial_support],
  split_ifs; simp
end

@[simp] lemma monomial_sum_index (h : f n 0 = 0) :
  (monomial n a).sum f = f n a :=
begin
  classical,
  rw monomial_sum,
  split_ifs; simp *
end

@[simp] lemma X_sum_index (h : f 1 0 = 0) : X.sum f = f 1 1 :=
begin
  classical,
  simp only [X, monomial_sum],
  split_ifs; cc
end

@[simp] lemma X_sum [nontrivial R] : X.sum f = f 1 1 :=
by { classical, simp [X, monomial_sum] }

lemma add_sum_index (h_zero : ∀ n, f n 0 = 0)
    (h_add : ∀ n r s, f n (r + s) = f n r + f n s) :
  (p + q).sum f = p.sum f + q.sum f :=
sum_add_index (λ _, h_zero _) (λ _ _ _, h_add _ _ _)

lemma mul_sum {S} [semiring S] {f : ℕ → R → S} {s : S} :
  s * p.sum f = p.sum (λ n a, s * f n a) :=
mul_sum _ _

lemma smul_sum_index (h0 : ∀ i, f i 0 = 0) :
  (a • p).sum f = p.sum (λ n b, f n (a * b)) :=
sum_smul_index (λ _, h0 _)

variable (p)
lemma sum_of_support_subset (s : finset ℕ) (hs : p.support ⊆ s) (h : ∀ i ∈ s, f i 0 = 0) :
  p.sum f = ∑ x in s, f x (p.coeff x) :=
have of_add.to_embedding.trans to_add.to_embedding = function.embedding.refl ℕ,
  by { ext, simp },
by simpa using @sum_of_support_subset _ _ _ _ _ p
  (s.map of_add.to_embedding)
  (by rwa [← finset.map_subset_map, finset.map_map, this, finset.map_refl])
  (λ n a, f n.to_add a)
  (λ i hi, h _ (by simpa using hi))
variable {p}

end sum

lemma mul_def : p * q = p.sum (λ i pi, q.sum (λ j qj, monomial (i + j) (pi * qj))) :=
by simp [sum_def, monoid_algebra.mul_def, support, monomial, finsupp.sum, coeff]

end semiring

section comm_semiring
variables [comm_semiring R]

instance : comm_semiring (polynomial R) := monoid_algebra.comm_semiring

end comm_semiring

section ring
variables [ring R]

instance : ring (polynomial R) := monoid_algebra.ring

@[simp] lemma coeff_neg (p : polynomial R) (n : ℕ) : coeff (-p) n = -coeff p n := rfl

@[simp]
lemma coeff_sub (p q : polynomial R) (n : ℕ) : coeff (p - q) n = coeff p n - coeff q n :=
rfl

@[simp] lemma monomial_neg (n : ℕ) (a : R) : monomial n (-a) = -(monomial n a) :=
by rw [eq_neg_iff_add_eq_zero, ←monomial_add, neg_add_self, monomial_zero_right]

@[simp] lemma support_neg {p : polynomial R} : (-p).support = p.support :=
by simp [support]

end ring

instance [comm_ring R] : comm_ring (polynomial R) := monoid_algebra.comm_ring

section nonzero_semiring

variables [semiring R] [nontrivial R]
instance : nontrivial (polynomial R) := monoid_algebra.nontrivial

lemma X_ne_zero : (X : polynomial R) ≠ 0 :=
mt (congr_arg (λ p, coeff p 1)) (by simp)

end nonzero_semiring

section repr
variables [semiring R]
local attribute [instance, priority 100] classical.prop_decidable

instance [has_repr R] : has_repr (polynomial R) :=
⟨λ p, if p = 0 then "0"
  else (p.support.sort (≤)).foldr
    (λ n a, a ++ (if a = "" then "" else " + ") ++
      if n = 0
        then "C (" ++ repr (coeff p n) ++ ")"
        else if n = 1
          then if (coeff p n) = 1 then "X" else "C (" ++ repr (coeff p n) ++ ") * X"
          else if (coeff p n) = 1 then "X ^ " ++ repr n
            else "C (" ++ repr (coeff p n) ++ ") * X ^ " ++ repr n) ""⟩

end repr

end polynomial
