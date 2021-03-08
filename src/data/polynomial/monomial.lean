/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.basic

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/

noncomputable theory

open finsupp multiplicative

namespace polynomial

universes u
variables {R : Type u} {a b : R} {m n : ℕ}
variables [semiring R] {p q r : polynomial R}

/--
`C a` is the constant polynomial `a`.
`C` is provided as a ring homomorphism.
-/
def C : R →+* polynomial R := monoid_algebra.single_one_ring_hom

lemma C_support [decidable_eq R] : (C a).support = if a = 0 then ∅ else {0} :=
if h : a = 0 then
  by simp [h]
else
  begin
    rw [support, support_single_ne_zero h] {md := tactic.transparency.semireducible},
    simp [h]
  end

@[simp] lemma monomial_zero_left (a : R) : monomial 0 a = C a := rfl

lemma C_0 : C (0 : R) = 0 := single_zero

lemma C_1 : C (1 : R) = 1 := rfl

lemma C_mul : C (a * b) = C a * C b := C.map_mul a b

lemma C_add : C (a + b) = C a + C b := C.map_add a b

@[simp] lemma C_bit0 : C (bit0 a) = bit0 (C a) := C_add

@[simp] lemma C_bit1 : C (bit1 a) = bit1 (C a) := by simp [bit1, C_bit0]

lemma C_pow : C (a ^ n) = C a ^ n := C.map_pow a n

@[simp]
lemma C_eq_nat_cast (n : ℕ) : C (n : R) = (n : polynomial R) :=
C.map_nat_cast n

@[simp]
lemma C_sum_index {a} {β} [add_comm_monoid β] {f : ℕ → R → β} (h : f 0 0 = 0) :
  (C a).sum f = f 0 a :=
sum_single_index h

lemma coeff_C : coeff (C a) n = ite (n = 0) a 0 :=
by simpa [eq_comm] using @coeff_monomial _ a n 0 _

@[simp] lemma coeff_C_zero : coeff (C a) 0 = a := coeff_monomial

lemma coeff_C_ne_zero (h : n ≠ 0) : (C a).coeff n = 0 :=
by rw [coeff_C, if_neg h]

theorem nontrivial.of_polynomial_ne (h : p ≠ q) : nontrivial R :=
⟨⟨0, 1, λ h01 : 0 = 1, h $
    by rw [← mul_one p, ← mul_one q, ← C_1, ← h01, C_0, mul_zero, mul_zero] ⟩⟩

lemma monomial_eq_C_mul_X : ∀{n}, monomial n a = C a * X^n
| 0     := (mul_one _).symm
| (n+1) :=
  calc monomial (n + 1) a = monomial n a * X : by { rw [X, monomial_mul_monomial, mul_one], }
    ... = (C a * X^n) * X : by rw [monomial_eq_C_mul_X]
    ... = C a * X^(n+1) : by simp only [pow_add, mul_assoc, pow_one]

lemma single_eq_C_mul_X {n} : single n a = (C a * X^(to_add n) : polynomial R) :=
by { rw [← monomial_eq_C_mul_X, monomial, of_add_to_add], refl }

lemma C_mul_X_eq_single {n} : (C a * X^n : polynomial R) = single (of_add n) a :=
by simpa using (@single_eq_C_mul_X _ a _ (of_add n)).symm

@[simp] lemma C_inj : C a = C b ↔ a = b :=
⟨λ h, coeff_C_zero.symm.trans (h.symm ▸ coeff_C_zero), congr_arg C⟩

@[simp] lemma C_eq_zero : C a = 0 ↔ a = 0 :=
calc C a = 0 ↔ C a = C 0 : by rw C_0
         ... ↔ a = 0 : C_inj

instance [nontrivial R] : infinite (polynomial R) :=
infinite.of_injective (λ i, monomial i 1)
  (λ m n h, by simpa using (single_eq_single_iff _ _ _ _).1 h)

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
calc monomial n a = monomial n (a * 1) : by simp
  ... = a • monomial n 1 : (smul_single' _ _ _).symm
  ... = a • X^n  : by rw X_pow_eq_monomial

lemma ring_hom_ext {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : ∀ a, f (C a) = g (C a)) (h₂ : f X = g X) : f = g :=
by { ext, exacts [h₁ _, h₂] }

@[ext] lemma ring_hom_ext' {S} [semiring S] {f g : polynomial R →+* S}
  (h₁ : f.comp C = g.comp C) (h₂ : f X = g X) : f = g :=
ring_hom_ext (ring_hom.congr_fun h₁) h₂

lemma sum_C_mul_X_eq (p : polynomial R) : p.sum (λn a, C a * X^n) = p :=
by simp only [sum, ← single_eq_C_mul_X, p.sum_single]

lemma sum_monomial_eq (p : polynomial R) : p.sum (λn a, monomial n a) = p :=
by simpa only [monomial_eq_C_mul_X] using sum_C_mul_X_eq _

end polynomial
