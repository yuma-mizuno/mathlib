import data.nat.choose.basic
import data.list.perm
import tactic
open_locale nat

/-- The multinomial coefficient for `[c1,...,cn]` is the coefficient in front of
`x1^c1 * ... * xn^cn` in `(x1 + ... + xn)^(c1 + ... + cn)`.  It counts the number of ways
of ordering objects of `n` types, with `ci` of type `i`, where objects within each type
are indistinguishable.  The binomial coefficient is `[a, b].binomial = (a + b).choose a`. -/
def list.multinomial (m : list ℕ) : ℕ := nat.factorial m.sum / (m.map nat.factorial).prod

namespace nat

lemma multinomial_dvd (m : list ℕ) : (m.map factorial).prod ∣ factorial m.sum :=
begin
  induction m,
  { simp, },
  { simp only [list.sum_cons, list.prod_cons, list.map],
    transitivity m_hd! * m_tl.sum!,
    exact mul_dvd_mul_left m_hd! m_ih,
    convert @factorial_mul_factorial_dvd_factorial (m_hd + m_tl.sum) m_hd _,
    exact (norm_num.sub_nat_pos (m_hd + list.sum m_tl) m_hd (list.sum m_tl) rfl).symm,
    exact le.intro rfl, },
end

lemma multinomial_perm (m m' : list ℕ) (h : list.perm m m') : m.multinomial = m'.multinomial :=
sorry

@[simp] lemma multinomial_nil : [].multinomial = 1 := rfl

@[simp] lemma multinomial_singleton (a : ℕ): [a].multinomial = 1 :=
by simp [list.multinomial, nat.div_self (factorial_pos a)]

@[simp] lemma multinomial_head_zero (m : list ℕ) : (0 :: m).multinomial = m.multinomial := rfl

variables {a b : ℕ}

lemma multinomial_symm (m : list ℕ) : (a :: b :: m).multinomial = (b :: a :: m).multinomial :=
by simp [list.multinomial, add_left_comm, mul_left_comm]

lemma binomial_eq : [a, b].multinomial = (a + b)! / (a! * b!) :=
by simp [list.multinomial]

lemma binomial_eq_choose : [a, b].multinomial = (a + b).choose a :=
by simp [list.multinomial, nat.choose_eq_factorial_div_factorial (nat.le.intro rfl)]

theorem binomial_spec : a! * b! * [a, b].multinomial = (a + b)! :=
begin
  rw binomial_eq_choose,
  convert choose_mul_factorial_mul_factorial (show a ≤ a + b, by simp) using 1,
  rw nat.sub_eq_of_eq_add rfl,
  simp [mul_assoc, mul_comm, mul_left_comm],
end

theorem binomial_symm : [a, b].multinomial = [b, a].multinomial :=
multinomial_symm []

@[simp] lemma binomial_zero_right (n : ℕ) : [n, 0].multinomial = 1 :=
by { rw binomial_symm, simp, }

@[simp] lemma multinomial_one_left (m : list ℕ) :
  (1 :: m).multinomial = m.sum.succ * m.multinomial :=
begin
  simp only [list.multinomial, list.sum_cons, one_mul, factorial, list.prod_cons, list.map],
  rw [add_comm, ←succ_eq_add_one], rw factorial_succ,
  rw nat.mul_div_assoc _ (multinomial_dvd _),
end

lemma binomial_one_left (n : ℕ) : [1, n].multinomial = n.succ :=
by simp

@[simp] lemma binomial_one_right (n : ℕ) : [n, 1].multinomial = n.succ :=
@binomial_symm 1 n ▸ binomial_one_left n

@[simp] lemma binomial_succ_succ :
  [a.succ, b.succ].multinomial = [a, b.succ].multinomial + [a.succ, b].multinomial :=
by { simp [binomial_eq_choose, succ_add, add_succ, choose_succ_succ] }

@[simp] lemma binomial_two_left' (n : ℕ) : [2, n].multinomial * 2 = n.succ * n.succ.succ :=
begin
  induction n with d hd, refl,
  rw [binomial_succ_succ, add_mul, hd, binomial_one_left],
  simp only [mul_succ, ← succ_eq_add_one, succ_mul],
  simp [mul_succ, succ_mul, succ_eq_add_one, add_assoc, add_left_comm],
end

lemma multinomial_pos (m : list ℕ): 0 < m.multinomial :=
begin
  dunfold list.multinomial,
  sorry
end

lemma binomial_pos : 0 < [a, b].multinomial :=
by { rw binomial_eq_choose,
     exact choose_pos (show a ≤ a + b, from le.intro rfl) }

lemma succ_mul_binomial : (a + b).succ * [a, b].multinomial = a.succ * [a.succ, b].multinomial :=
begin
  simp [binomial_eq_choose],
  rw mul_comm a.succ,
  convert succ_mul_choose_eq (a + b) a,
  exact succ_add a b,
end

lemma succ_mul_binomial' : (a + b).succ * [a, b].multinomial = b.succ * [a, b.succ].multinomial :=
by rw [binomial_symm, add_comm, succ_mul_binomial, binomial_symm]

lemma succ_mul_binomial'' : a.succ * [a.succ, b].multinomial = b.succ * [a, b.succ].multinomial :=
by rw [← succ_mul_binomial, succ_mul_binomial']

-- this is strictly stronger than choose_le_succ_of_lt_half_left (edge cases)
lemma binomial_succ_le (h : a ≤ b) : [a, b.succ].multinomial ≤ [a.succ, b].multinomial :=
begin
  rw ← _root_.mul_le_mul_left
    (show 0 < a.succ! * b.succ!, from mul_pos (factorial_pos _) (factorial_pos _)),
  suffices : a.succ * (a! * b.succ! * [a, b.succ].multinomial) ≤ b.succ * (a.succ! * b! * [a.succ, b].multinomial),
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
  (h3 : a + d = b + c) : [a, d].multinomial ≤ [b, c].multinomial :=
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
