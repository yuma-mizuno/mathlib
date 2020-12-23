-- binomial

import data.nat.choose.basic
import tactic
open_locale nat

namespace nat

def binomial (a b : ℕ) : ℕ := (a + b).choose a

variables {a b : ℕ}

theorem binomial_def : binomial a b = (a + b)! / (a! * b!) :=
by {unfold binomial,
  simp [choose_eq_factorial_div_factorial (le.intro rfl)] }

theorem binomial_spec : a! * b! * binomial a b = (a + b)! :=
by {unfold binomial,
  convert choose_mul_factorial_mul_factorial (show a ≤ a + b, by simp) using 1,
  rw [nat.sub_eq_of_eq_add rfl, mul_comm, ← mul_assoc]}

theorem binomial_symm : binomial a b = binomial b a :=
by { simp [binomial_def, add_comm, mul_comm] }

@[simp] lemma binomial_zero_right (n : ℕ) : binomial n 0 = 1 := choose_self n

@[simp] lemma binomial_zero_left (n : ℕ) : binomial 0 n = 1 := @binomial_symm n 0 ▸ binomial_zero_right n

@[simp] lemma binomial_one_left (n : ℕ) : binomial 1 n = n.succ :=
by {unfold binomial,
  convert choose_one_right n.succ,
  apply add_comm }

@[simp] lemma binomial_one_right (n : ℕ) : binomial n 1 = n.succ := @binomial_symm 1 n ▸ binomial_one_left n

@[simp] lemma binomial_succ_succ : binomial a.succ b.succ = binomial a b.succ + binomial a.succ b :=
by {unfold binomial,
  convert choose_succ_succ (a + b + 1) a using 3;
  simp [succ_add, ← succ_eq_add_one ] }

@[simp] lemma binomial_two_left' (n : ℕ) : binomial 2 n * 2 = n.succ * n.succ.succ :=
begin
  induction n with d hd, refl,
  rw [binomial_succ_succ, add_mul, hd, binomial_one_left],
  simp only [mul_succ, ← succ_eq_add_one, succ_mul],
  simp [mul_succ, succ_mul, succ_eq_add_one, add_assoc, add_left_comm]
end

lemma binomial_pos : 0 < binomial a b := choose_pos (show a ≤ a + b, from le.intro rfl)

lemma succ_mul_binomial : (a + b).succ * binomial a b = a.succ * binomial a.succ b :=
begin
  unfold binomial,
  rw mul_comm a.succ,
  convert succ_mul_choose_eq (a + b) a,
  exact succ_add a b,
end

lemma succ_mul_binomial' : (a + b).succ * binomial a b = b.succ * binomial a b.succ :=
by rw [binomial_symm, add_comm, succ_mul_binomial, binomial_symm]

lemma succ_mul_binomial'' : a.succ * binomial a.succ b = b.succ * binomial a b.succ :=
by rw [← succ_mul_binomial, succ_mul_binomial']

-- this is strictly stronger than choose_le_succ_of_lt_half_left (edge cases)
lemma binomial_succ_le (h : a ≤ b) : a.binomial b.succ <= a.succ.binomial b :=
begin
  rw ← _root_.mul_le_mul_left
    (show 0 < a.succ! * b.succ!, from mul_pos (factorial_pos _) (factorial_pos _)),
  suffices : a.succ * (a! * b.succ! * binomial a b.succ) ≤ b.succ * (a.succ! * b! * binomial a.succ b),
  convert this using 1,
  { rw factorial_succ a,
    ring },
  { rw factorial_succ b, ring },
  { rw [binomial_spec, binomial_spec, succ_add, add_succ],
    mono,
    { exact zero_le _},
    { exact succ_le_succ h } }
end

lemma binomial_le_middle {a b c d : ℕ} (h1 : a ≤ b) (h2 : b ≤ c)
  (h3 : a + d = b + c) : binomial a d ≤ binomial b c :=
begin
  rw le_iff_exists_add at h1,
  cases h1 with n hn,
  induction n with n hn hm generalizing b c,
  { simp * at * },
  cases b,
  { cases hn_1 },
  have hb : b = a + n,
  { rw [← succ_inj', hn_1, add_succ] },
  rw [succ_add, ← add_succ] at h3,
  exact le_trans (hn (le_trans (le_succ _) (le_trans h2 (le_succ _))) h3 hb)
    (binomial_succ_le (le_trans (le_succ _) h2)),
end

end nat
