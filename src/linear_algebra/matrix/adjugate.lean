/-
Copyright (c) 2019 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.associated
import algebra.regular.basic
import data.matrix.notation
import linear_algebra.matrix.polynomial
import tactic.linarith
import tactic.ring_exp

/-!
# Cramer's rule and adjugate matrices

The adjugate matrix is the transpose of the cofactor matrix.
It is calculated with Cramer's rule, which we introduce first.
The vectors returned by Cramer's rule are given by the linear map `cramer`,
which sends a matrix `A` and vector `b` to the vector consisting of the
determinant of replacing the `i`th column of `A` with `b` at index `i`
(written as `(A.update_column i b).det`).
Using Cramer's rule, we can compute for each matrix `A` the matrix `adjugate A`.
The entries of the adjugate are the determinants of each minor of `A`.
Instead of defining a minor to be `A` with row `i` and column `j` deleted, we
replace the `i`th row of `A` with the `j`th basis vector; this has the same
determinant as the minor but more importantly equals Cramer's rule applied
to `A` and the `j`th basis vector, simplifying the subsequent proofs.
We prove the adjugate behaves like `det A • A⁻¹`.

## Main definitions

 * `matrix.cramer A b`: the vector output by Cramer's rule on `A` and `b`.
 * `matrix.adjugate A`: the adjugate (or classical adjoint) of the matrix `A`.

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

cramer, cramer's rule, adjugate
-/

namespace matrix
universes u v
variables {n : Type u} [decidable_eq n] [fintype n] {α : Type v} [comm_ring α]
open_locale matrix big_operators
open equiv equiv.perm finset

section cramer
/-!
  ### `cramer` section

  Introduce the linear map `cramer` with values defined by `cramer_map`.
  After defining `cramer_map` and showing it is linear,
  we will restrict our proofs to using `cramer`.
-/
variables (A : matrix n n α) (b : n → α)

/--
  `cramer_map A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer_map A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer_map A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer_map` is well-defined but not necessarily useful.
-/
def cramer_map (i : n) : α := (A.update_column i b).det

lemma cramer_map_is_linear (i : n) : is_linear_map α (λ b, cramer_map A b i) :=
{ map_add := det_update_column_add _ _,
  map_smul := det_update_column_smul _ _ }

lemma cramer_is_linear : is_linear_map α (cramer_map A) :=
begin
  split; intros; ext i,
  { apply (cramer_map_is_linear A i).1 },
  { apply (cramer_map_is_linear A i).2 }
end

/--
  `cramer A b i` is the determinant of the matrix `A` with column `i` replaced with `b`,
  and thus `cramer A b` is the vector output by Cramer's rule on `A` and `b`.

  If `A ⬝ x = b` has a unique solution in `x`, `cramer A` sends the vector `b` to `A.det • x`.
  Otherwise, the outcome of `cramer` is well-defined but not necessarily useful.
 -/
def cramer (A : matrix n n α) : (n → α) →ₗ[α] (n → α) :=
is_linear_map.mk' (cramer_map A) (cramer_is_linear A)

lemma cramer_apply (i : n) : cramer A b i = (A.update_column i b).det := rfl

lemma cramer_transpose_row_self (i : n) :
  Aᵀ.cramer (A i) = pi.single i A.det :=
begin
  ext j,
  rw [cramer_apply, pi.single_apply],
  split_ifs with h,
  { -- i = j: this entry should be `A.det`
    subst h,
    simp only [update_column_transpose, det_transpose, update_row, function.update_eq_self] },
  { -- i ≠ j: this entry should be 0
    rw [update_column_transpose, det_transpose],
    apply det_zero_of_row_eq h,
    rw [update_row_self, update_row_ne (ne.symm h)] }
end

lemma cramer_row_self (i : n) (h : ∀ j, b j = A j i) :
  A.cramer b = pi.single i A.det :=
begin
  rw [← transpose_transpose A, det_transpose],
  convert cramer_transpose_row_self Aᵀ i,
  exact funext h
end

@[simp] lemma cramer_one : cramer (1 : matrix n n α) = 1 :=
begin
  ext i j,
  convert congr_fun (cramer_row_self (1 : matrix n n α) (pi.single i 1) i _) j,
  { simp },
  { intros j, rw [matrix.one_eq_pi_single, pi.single_comm] }
end

lemma cramer_smul (r : α) (A : matrix n n α) :
  cramer (r • A) = r ^ (fintype.card n - 1) • cramer A :=
linear_map.ext $ λ b, funext $ λ _, det_update_column_smul' _ _ _ _

@[simp] lemma cramer_subsingleton_apply [subsingleton n] (A : matrix n n α) (b : n → α) (i : n) :
  cramer A b i = b i :=
by rw [cramer_apply, det_eq_elem_of_subsingleton _ i, update_column_self]

lemma cramer_zero [nontrivial n] : cramer (0 : matrix n n α) = 0 :=
begin
  ext i j,
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j,
  apply det_eq_zero_of_column_eq_zero j',
  intro j'',
  simp [update_column_ne hj'],
end

/-- Use linearity of `cramer` to take it out of a summation. -/
lemma sum_cramer {β} (s : finset β) (f : β → n → α) :
  ∑ x in s, cramer A (f x) = cramer A (∑ x in s, f x) :=
(linear_map.map_sum (cramer A)).symm

/-- Use linearity of `cramer` and vector evaluation to take `cramer A _ i` out of a summation. -/
lemma sum_cramer_apply {β} (s : finset β) (f : n → β → α) (i : n) :
∑ x in s, cramer A (λ j, f j x) i = cramer A (λ (j : n), ∑ x in s, f j x) i :=
calc ∑ x in s, cramer A (λ j, f j x) i
    = (∑ x in s, cramer A (λ j, f j x)) i : (finset.sum_apply i s _).symm
... = cramer A (λ (j : n), ∑ x in s, f j x) i :
  by { rw [sum_cramer, cramer_apply], congr' with j, apply finset.sum_apply }

end cramer

section adjugate
/-!
### `adjugate` section

Define the `adjugate` matrix and a few equations.
These will hold for any matrix over a commutative ring.
-/

/-- The adjugate matrix is the transpose of the cofactor matrix.

  Typically, the cofactor matrix is defined by taking the determinant of minors,
  i.e. the matrix with a row and column removed.
  However, the proof of `mul_adjugate` becomes a lot easier if we define the
  minor as replacing a column with a basis vector, since it allows us to use
  facts about the `cramer` map.
-/
def adjugate (A : matrix n n α) : matrix n n α := λ i, cramer Aᵀ (pi.single i 1)

lemma adjugate_def (A : matrix n n α) :
  adjugate A = λ i, cramer Aᵀ (pi.single i 1) := rfl

lemma adjugate_apply (A : matrix n n α) (i j : n) :
  adjugate A i j = (A.update_row j (pi.single i 1)).det :=
by { rw adjugate_def, simp only, rw [cramer_apply, update_column_transpose, det_transpose], }

lemma adjugate_transpose (A : matrix n n α) : (adjugate A)ᵀ = adjugate (Aᵀ) :=
begin
  ext i j,
  rw [transpose_apply, adjugate_apply, adjugate_apply, update_row_transpose, det_transpose],
  rw [det_apply', det_apply'],
  apply finset.sum_congr rfl,
  intros σ _,
  congr' 1,

  by_cases i = σ j,
  { -- Everything except `(i , j)` (= `(σ j , j)`) is given by A, and the rest is a single `1`.
    congr; ext j',
    subst h,
    have : σ j' = σ j ↔ j' = j := σ.injective.eq_iff,
    rw [update_row_apply, update_column_apply],
    simp_rw this,
    rw [←dite_eq_ite, ←dite_eq_ite],
    congr' 1 with rfl,
    rw [pi.single_eq_same, pi.single_eq_same], },
  { -- Otherwise, we need to show that there is a `0` somewhere in the product.
    have : (∏ j' : n, update_column A j (pi.single i 1) (σ j') j') = 0,
    { apply prod_eq_zero (mem_univ j),
      rw [update_column_self, pi.single_eq_of_ne' h], },
    rw this,
    apply prod_eq_zero (mem_univ (σ⁻¹ i)),
    erw [apply_symm_apply σ i, update_row_self],
    apply pi.single_eq_of_ne,
    intro h',
    exact h ((symm_apply_eq σ).mp h') }
end

/-- Since the map `b ↦ cramer A b` is linear in `b`, it must be multiplication by some matrix. This
matrix is `A.adjugate`. -/
lemma cramer_eq_adjugate_mul_vec (A : matrix n n α) (b : n → α) :
  cramer A b = A.adjugate.mul_vec b :=
begin
  nth_rewrite 1 ← A.transpose_transpose,
  rw [← adjugate_transpose, adjugate_def],
  have : b = ∑ i, (b i) • (pi.single i 1),
  { refine (pi_eq_sum_univ b).trans _, congr' with j, simp [pi.single_apply, eq_comm], congr, },
  nth_rewrite 0 this, ext k,
  simp [mul_vec, dot_product, mul_comm],
end

lemma mul_adjugate_apply (A : matrix n n α) (i j k) :
  A i k * adjugate A k j = cramer Aᵀ (pi.single k (A i k)) j :=
begin
  erw [←smul_eq_mul, ←pi.smul_apply, ←linear_map.map_smul, ←pi.single_smul', smul_eq_mul, mul_one],
end

lemma mul_adjugate (A : matrix n n α) : A ⬝ adjugate A = A.det • 1 :=
begin
  ext i j,
  rw [mul_apply, pi.smul_apply, pi.smul_apply, one_apply, smul_eq_mul, mul_boole],
  simp [mul_adjugate_apply, sum_cramer_apply, cramer_transpose_row_self, pi.single_apply, eq_comm]
end

lemma adjugate_mul (A : matrix n n α) : adjugate A ⬝ A = A.det • 1 :=
calc adjugate A ⬝ A = (Aᵀ ⬝ (adjugate Aᵀ))ᵀ :
  by rw [←adjugate_transpose, ←transpose_mul, transpose_transpose]
... = A.det • 1 : by rw [mul_adjugate (Aᵀ), det_transpose, transpose_smul, transpose_one]

lemma adjugate_smul (r : α) (A : matrix n n α) :
  adjugate (r • A) = r ^ (fintype.card n - 1) • adjugate A :=
begin
  rw [adjugate, adjugate, transpose_smul, cramer_smul],
  refl,
end

/-- A stronger form of **Cramer's rule** that allows us to solve some instances of `A ⬝ x = b` even
if the determinant is not a unit. A sufficient (but still not necessary) condition is that `A.det`
divides `b`. -/
@[simp] lemma mul_vec_cramer (A : matrix n n α) (b : n → α) :
  A.mul_vec (cramer A b) = A.det • b :=
by rw [cramer_eq_adjugate_mul_vec, mul_vec_mul_vec, mul_adjugate, smul_mul_vec_assoc, one_mul_vec]

/-- `det_adjugate_of_cancel` is an auxiliary lemma for computing `(adjugate A).det`,
  used in `det_adjugate_eq_one` and `det_adjugate_of_is_unit`.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_cancel` covers the case that `det A` cancels
  on the left of the equation `A.det * b = A.det ^ n`.
-/
lemma det_adjugate_of_cancel {A : matrix n n α}
  (h : ∀ b, A.det * b = A.det ^ fintype.card n → b = A.det ^ (fintype.card n - 1)) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
h (adjugate A).det (calc A.det * (adjugate A).det = (A ⬝ adjugate A).det   : (det_mul _ _).symm
                                              ... = A.det ^ fintype.card n : by simp [mul_adjugate])

lemma adjugate_subsingleton [subsingleton n] (A : matrix n n α) : adjugate A = 1 :=
begin
  ext i j,
  simp [subsingleton.elim i j, adjugate_apply, det_eq_elem_of_subsingleton _ i]
end

lemma adjugate_eq_one_of_card_eq_one {A : matrix n n α} (h : fintype.card n = 1) : adjugate A = 1 :=
begin
  haveI : subsingleton n := fintype.card_le_one_iff_subsingleton.mp h.le,
  exact adjugate_subsingleton _
end

@[simp] lemma adjugate_zero [nontrivial n] : adjugate (0 : matrix n n α) = 0 :=
begin
  ext i j,
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j,
  apply det_eq_zero_of_column_eq_zero j',
  intro j'',
  simp [update_column_ne hj'],
end

@[simp] lemma adjugate_one : adjugate (1 : matrix n n α) = 1 :=
by { ext, simp [adjugate_def, matrix.one_apply, pi.single_apply, eq_comm] }

lemma det_adjugate_eq_one {A : matrix n n α} (h : A.det = 1) : (adjugate A).det = 1 :=
calc (adjugate A).det
    = A.det ^ (fintype.card n - 1) : det_adjugate_of_cancel (λ b hb, by simpa [h] using hb)
... = 1                            : by rw [h, one_pow]

/-- `det_adjugate_of_is_unit` gives the formula for `(adjugate A).det` if `A.det` has an inverse.

  The formula for the determinant of the adjugate of an `n` by `n` matrix `A`
  is in general `(adjugate A).det = A.det ^ (n - 1)`, but the proof differs in several cases.
  This lemma `det_adjugate_of_is_unit` covers the case that `det A` has an inverse.
-/
lemma det_adjugate_of_is_unit {A : matrix n n α} (h : is_unit A.det) :
  (adjugate A).det = A.det ^ (fintype.card n - 1) :=
begin
  rcases is_unit_iff_exists_inv'.mp h with ⟨a, ha⟩,
  by_cases card_lt_zero : fintype.card n ≤ 0,
  { have h : fintype.card n = 0 := by linarith,
    simp [det_eq_one_of_card_eq_zero h] },
  have zero_lt_card : 0 < fintype.card n := by linarith,
  have n_nonempty : nonempty n := fintype.card_pos_iff.mp zero_lt_card,

  by_cases card_lt_one : fintype.card n ≤ 1,
  { have h : fintype.card n = 1 := by linarith,
    simp [h, adjugate_eq_one_of_card_eq_one h] },
  have one_lt_card : 1 < fintype.card n := by linarith,
  have zero_lt_card_sub_one : 0 < fintype.card n - 1 :=
    (tsub_lt_tsub_iff_right (refl 1)).mpr one_lt_card,

  apply det_adjugate_of_cancel,
  intros b hb,
  calc b = a * (det A ^ (fintype.card n - 1 + 1)) :
       by rw [←one_mul b, ←ha, mul_assoc, hb, tsub_add_cancel_of_le zero_lt_card.nat_succ_le]
     ... = a * det A * det A ^ (fintype.card n - 1) : by ring_exp
     ... = det A ^ (fintype.card n - 1) : by rw [ha, one_mul]
end

@[simp] lemma adjugate_fin_zero (A : matrix (fin 0) (fin 0) α) : adjugate A = 0 :=
@subsingleton.elim _ matrix.subsingleton_of_empty_left _ _

@[simp] lemma adjugate_fin_one (A : matrix (fin 1) (fin 1) α) : adjugate A = 1 :=
adjugate_subsingleton A

lemma adjugate_fin_two (A : matrix (fin 2) (fin 2) α) :
  adjugate A = ![![A 1 1, -A 0 1], ![-A 1 0, A 0 0]] :=
begin
  ext i j,
  rw [adjugate_apply, det_fin_two],
  fin_cases i with [0, 1]; fin_cases j with [0, 1];
  simp only [nat.one_ne_zero, one_mul, fin.one_eq_zero_iff, pi.single_eq_same, zero_mul,
    fin.zero_eq_one_iff, sub_zero, pi.single_eq_of_ne, ne.def, not_false_iff, update_row_self,
    update_row_ne, cons_val_zero, mul_zero, mul_one, zero_sub, cons_val_one, head_cons],
end

@[simp] lemma adjugate_fin_two' (a b c d : α) :
  adjugate ![![a, b], ![c, d]] = ![![d, -b], ![-c, a]] :=
adjugate_fin_two _

lemma _root_.ring_hom.map_adjugate {R S : Type*} [comm_ring R] [comm_ring S] (f : R →+* S)
  (M : matrix n n R) : f.map_matrix M.adjugate = matrix.adjugate (f.map_matrix M) :=
begin
  ext i k,
  have : pi.single i (1 : S) = f ∘ pi.single i 1,
  { rw ←f.map_one,
    exact pi.single_op (λ i, f) (λ i, f.map_zero) i (1 : R) },
  rw [adjugate_apply, ring_hom.map_matrix_apply, map_apply, ring_hom.map_matrix_apply,
      this, ←map_update_row, ←ring_hom.map_matrix_apply, ←ring_hom.map_det, ←adjugate_apply]
end

lemma adjugate_conj_transpose [star_ring α] (A : matrix n n α) : A.adjugateᴴ = adjugate (Aᴴ) :=
begin
  dsimp only [conj_transpose],
  have : Aᵀ.adjugate.map star = adjugate (Aᵀ.map star) :=
    ((star_ring_aut : α ≃+* α).to_ring_hom.map_adjugate Aᵀ),
  rw [A.adjugate_transpose, this],
end

lemma is_regular_of_is_left_regular_det {A : matrix n n α} (hA : is_left_regular A.det) :
  is_regular A :=
begin
  split,
  { intros B C h,
    refine hA.matrix _,
    rw [←matrix.one_mul B, ←matrix.one_mul C, ←matrix.smul_mul, ←matrix.smul_mul, ←adjugate_mul,
        matrix.mul_assoc, matrix.mul_assoc, ←mul_eq_mul A, h, mul_eq_mul] },
  { intros B C h,
    simp only [mul_eq_mul] at h,
    refine hA.matrix _,
    rw [←matrix.mul_one B, ←matrix.mul_one C, ←matrix.mul_smul, ←matrix.mul_smul, ←mul_adjugate,
        ←matrix.mul_assoc, ←matrix.mul_assoc, h] }
end

lemma adjugate_mul_distrib_aux (A B : matrix n n α)
  (hA : is_left_regular A.det)
  (hB : is_left_regular B.det) :
  adjugate (A ⬝ B) = adjugate B ⬝ adjugate A :=
begin
  have hAB : is_left_regular (A ⬝ B).det,
  { rw [det_mul],
    exact hA.mul hB },
  refine (is_regular_of_is_left_regular_det hAB).left _,
  rw [mul_eq_mul, mul_adjugate, mul_eq_mul, matrix.mul_assoc, ←matrix.mul_assoc B, mul_adjugate,
      smul_mul, matrix.one_mul, mul_smul, mul_adjugate, smul_smul, mul_comm, ←det_mul]
end

/--
Proof follows from "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3
-/
lemma adjugate_mul_distrib (A B : matrix n n α) : adjugate (A ⬝ B) = adjugate B ⬝ adjugate A :=
begin
  casesI subsingleton_or_nontrivial α,
  { simp },
  let g : matrix n n α → matrix n n (polynomial α) :=
    λ M, M.map polynomial.C + (polynomial.X : polynomial α) • 1,
  let f' : matrix n n (polynomial α) →+* matrix n n α := (polynomial.eval_ring_hom 0).map_matrix,
  have f'_inv : ∀ M, f' (g M) = M,
  { intro,
    ext,
    simp [f', g], },
  have f'_adj : ∀ (M : matrix n n α), f' (adjugate (g M)) = adjugate M,
  { intro,
    rw [ring_hom.map_adjugate, f'_inv] },
  have f'_g_mul : ∀ (M N : matrix n n α), f' (g M ⬝ g N) = M ⬝ N,
  { intros,
    rw [←mul_eq_mul, ring_hom.map_mul, f'_inv, f'_inv, mul_eq_mul] },
  have hu : ∀ (M : matrix n n α), is_regular (g M).det,
  { intros M,
    refine polynomial.monic.is_regular _,
    simp only [g, polynomial.monic.def, ←polynomial.leading_coeff_det_X_one_add_C M, add_comm] },
  rw [←f'_adj, ←f'_adj, ←f'_adj, ←mul_eq_mul (f' (adjugate (g B))), ←f'.map_mul, mul_eq_mul,
      ←adjugate_mul_distrib_aux _ _ (hu A).left (hu B).left, ring_hom.map_adjugate,
      ring_hom.map_adjugate, f'_inv, f'_g_mul]
end

@[simp] lemma adjugate_pow (A : matrix n n α) (k : ℕ) :
  adjugate (A ^ k) = (adjugate A) ^ k :=
begin
  induction k with k IH,
  { simp },
  { rw [pow_succ', mul_eq_mul, adjugate_mul_distrib, IH, ←mul_eq_mul, pow_succ] }
end

end adjugate

end matrix
