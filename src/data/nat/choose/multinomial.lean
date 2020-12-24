import data.nat.choose.basic
import data.list.perm
import tactic
open_locale nat

namespace nat

/-- The multinomial coefficient for `[c1,...,cn]` is the coefficient in front of
`x1^c1 * ... * xn^cn` in `(x1 + ... + xn)^(c1 + ... + cn)`.  It counts the number of ways
of ordering objects of `n` types, with `ci` of type `i`, where objects within each type
are indistinguishable.  The binomial coefficient is `[a, b].binomial = (a + b).choose a`. -/
def multinomial (m : list ℕ) : ℕ := m.sum! / (m.map nat.factorial).prod

lemma prod_factorial_dvd_factorial_sum (m : list ℕ) : (m.map factorial).prod ∣ factorial m.sum :=
begin
  induction m,
  { simp, },
  { simp only [list.sum_cons, list.prod_cons, list.map],
    transitivity m_hd! * m_tl.sum!,
    { exact mul_dvd_mul_left m_hd! m_ih, },
    { convert @factorial_mul_factorial_dvd_factorial (m_hd + m_tl.sum) m_hd (le.intro rfl),
      rw nat.add_sub_cancel_left, }, },
end

lemma prod_factorial_pos (m : list ℕ) : 0 < (m.map factorial).prod :=
begin
  induction m,
  { simp only [succ_pos', list.prod_nil, list.map], },
  { simp only [m_ih, factorial_pos, zero_lt_mul_right, list.prod_cons, list.map], },
end

lemma multinomial_pos (m : list ℕ): 0 < multinomial m :=
nat.div_pos (le_of_dvd (factorial_pos _) (prod_factorial_dvd_factorial_sum m))
  (prod_factorial_pos m)

lemma multinomial_spec (m : list ℕ) : (m.map nat.factorial).prod * multinomial m = m.sum! :=
begin
  dunfold multinomial,
  rw [←nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum m),
      mul_comm, nat.mul_div_cancel _ (prod_factorial_pos _)],
end

lemma multinomial_perm (m m' : list ℕ) (h : list.perm m m') : multinomial m = multinomial m' :=
by { dunfold multinomial, rw [list.perm.sum_eq h, list.perm.prod_eq (list.perm.map _ h)] }

@[simp] lemma multinomial_nil : multinomial [] = 1 := rfl

@[simp] lemma multinomial_singleton (a : ℕ): multinomial [a] = 1 :=
by simp [multinomial, nat.div_self (factorial_pos a)]

@[simp] lemma multinomial_head_zero (m : list ℕ) : multinomial (0 :: m) = multinomial m := rfl

variables {a b : ℕ}

lemma multinomial_swap (m : list ℕ) : multinomial (a :: b :: m) = multinomial (b :: a :: m) :=
multinomial_perm _ _ (list.perm.swap _ _ _)

lemma binomial_eq : multinomial [a, b] = (a + b)! / (a! * b!) :=
by simp [multinomial]

lemma binomial_eq_choose : multinomial [a, b] = (a + b).choose a :=
by simp [multinomial, nat.choose_eq_factorial_div_factorial (nat.le.intro rfl)]

theorem binomial_spec : a! * b! * multinomial [a, b] = (a + b)! :=
by { have h := multinomial_spec [a, b], simpa using h, }

theorem binomial_swap : multinomial [a, b] = multinomial [b, a] :=
multinomial_swap []

@[simp] lemma binomial_zero_right (n : ℕ) : multinomial [n, 0] = 1 :=
by { rw binomial_swap, simp, }

@[simp] lemma multinomial_one_left (m : list ℕ) :
  multinomial (1 :: m) = m.sum.succ * multinomial m :=
begin
  simp only [multinomial, list.sum_cons, one_mul, factorial, list.prod_cons, list.map],
  rw [add_comm, ←succ_eq_add_one, factorial_succ,
      nat.mul_div_assoc _ (prod_factorial_dvd_factorial_sum _)],
end

lemma binomial_one_left (n : ℕ) : multinomial [1, n] = n.succ :=
by simp

@[simp] lemma binomial_one_right (n : ℕ) : multinomial [n, 1] = n.succ :=
@binomial_swap 1 n ▸ binomial_one_left n

@[simp] lemma binomial_succ_succ :
  multinomial [a.succ, b.succ] = multinomial [a, b.succ] + multinomial [a.succ, b] :=
by simp [binomial_eq_choose, succ_add, add_succ, choose_succ_succ]

@[simp] lemma binomial_two_left' (n : ℕ) : multinomial [2, n] * 2 = n.succ * n.succ.succ :=
begin
  induction n with d hd, refl,
  rw [binomial_succ_succ, add_mul, hd, binomial_one_left],
  simp only [mul_succ, ← succ_eq_add_one, succ_mul],
  simp [mul_succ, succ_mul, succ_eq_add_one, add_assoc, add_left_comm],
end

lemma succ_mul_binomial : (a + b).succ * multinomial [a, b] = a.succ * multinomial [a.succ, b] :=
begin
  rw [binomial_eq_choose, binomial_eq_choose, mul_comm a.succ],
  convert succ_mul_choose_eq (a + b) a,
  exact succ_add a b,
end

lemma succ_mul_binomial' : (a + b).succ * multinomial [a, b] = b.succ * multinomial [a, b.succ] :=
by rw [binomial_swap, add_comm, succ_mul_binomial, binomial_swap]

lemma succ_mul_binomial'' : a.succ * multinomial [a.succ, b] = b.succ * multinomial [a, b.succ] :=
by rw [← succ_mul_binomial, succ_mul_binomial']

-- this is strictly stronger than choose_le_succ_of_lt_half_left (edge cases)
lemma binomial_succ_le (h : a ≤ b) : multinomial [a, b.succ] ≤ multinomial [a.succ, b] :=
begin
  rw ← _root_.mul_le_mul_left
    (show 0 < a.succ! * b.succ!, from mul_pos (factorial_pos _) (factorial_pos _)),
  suffices : a.succ * (a! * b.succ! * multinomial [a, b.succ]) ≤ b.succ * (a.succ! * b! * multinomial [a.succ, b]),
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
  (h3 : a + d = b + c) : multinomial [a, d] ≤ multinomial [b, c] :=
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
