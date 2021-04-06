import linear_algebra.determinant
import data.matrix.notation

#check 1

open_locale big_operators

section pi_block_diagonal

variables {α : Type*} [has_zero α]
variables {o : Type*} [fintype o] [decidable_eq o]
variables {n : o → Type*} [∀ i, fintype (n i)] [∀ i, decidable_eq (n i)]
variables {m : o → Type*} [∀ i, fintype (m i)] [∀ i, decidable_eq (m i)]
variables (M N : Π i, matrix (m i) (n i) α) [decidable_eq o]

def matrix.block_diagonal' : matrix (Σ i, m i) (Σ i, n i) α
| ⟨k, i⟩ ⟨k', j⟩ := if h : k = k' then M k i (cast (congr_arg n h.symm) j) else 0

@[simp]
lemma matrix.block_diagonal'_apply_eq (i mi ni) :
  matrix.block_diagonal' M ⟨i, mi⟩ ⟨i, ni⟩ = M i mi ni := dif_pos rfl

#check matrix.block_diagonal_apply_eq

end pi_block_diagonal

variables {n R : Type*} [fintype n] [decidable_eq n] [comm_ring R]

def is_triangular (A : matrix n n R) : Prop :=
A.det = ∏ i, A i i

@[simp] lemma fin.cast_succ_one {n : ℕ} : fin.cast_succ (1 : fin n.succ.succ) = 1 :=
begin
  ext,
  simp,
end

@[simp] lemma fin.zero_ne_succ {n : ℕ} (i : fin n) : (0 : fin n.succ) ≠ i.succ :=
begin
  intro h,
  rw fin.ext_iff at h,
  simpa using h,
end

/-- A jordan block is a matrix with a repeated value on the diagonal, and ones in the
super-diagonal, such as the matrix
```
![![x, 1, 0],
  ![0, x, 1],
  ![0, 0, x]]
```
-/
def jordan_block (n : ℕ) (eig : R) : matrix (fin n) (fin n) R
| i j := if i = j then eig else
         if j.cast_succ = i.succ then 1 else
         0

/-- A matrix is jordan-normal if it decomposes into a diagonal of `jordan_block`s. -/
def is_jordan_normal (A : matrix n n R) : Prop :=
∃
  (p : ℕ)  -- number of blocks
  (k : fin p → ℕ) -- dimension of each block
  (eig : fin p → R) -- eigenvalue of each block
  (ind : n ≃ (Σ i, fin (k i))), -- mapping into the diagonal
    A = matrix.minor (by exact matrix.block_diagonal' (λ i, jordan_block _ (eig i))) ind ind

/- A `jordan_block` is obviously `jordan_normal`. -/
@[simp] lemma is_jordan_normal_jordan_block (n : ℕ) (eig : R) :
  is_jordan_normal (jordan_block n eig) :=
⟨1, ![n], ![eig], begin
  refine ⟨⟨λ x, ⟨0, x⟩, λ x, _, _, _⟩, _⟩,
  { cases x,
    rw subsingleton.elim x_fst 0 at x_snd,
    exact x_snd, },
  { intro x, simp },
  { intro x, ext1,
    { simp, },
    { cases x, simp } },
  ext,
  simp [matrix.minor],
  refl,
end⟩

lemma jordan_block_one (eig : R) : jordan_block 1 eig = ![![eig]] :=
begin
  ext i j,
  unfold jordan_block,
  split_ifs with h₁ h₂ h₃; simp * at *,
end

/-- This lemma acts as a sanity check. -/
lemma jordan_block_two (eig : R) : jordan_block 2 eig =
  ![![eig, 1],
    ![0, eig]] :=
begin
  ext i j,
  unfold jordan_block,
  split_ifs with h₁ h₂ h₃; fin_cases i; fin_cases j; simp * at *,
end
