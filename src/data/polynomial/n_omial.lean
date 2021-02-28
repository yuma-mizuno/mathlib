/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import data.polynomial.eval

/-!
# Bundled Trinomials

In this file we define an bundled trinomial, which are easier to
work with than a sum of monomials.

## Main definitions

- `polynomial.trinomial`
- `trinomial.of_polynomial`: unbundle a trinomial
- `polynomial.to_trinomial`: bundle a trinomial

## Main results

- `reverse'_irreducible_test'`: an irreducibility criterion for unit trinomials
- `reverse'_irreducible_test''`: an irreducibility criterion for unit trinomials
- `selmer_irreducible`: the polynomial `X ^ n - X - 1` is irreducible for all `n ≠ 1`

-/

open_locale big_operators

namespace polynomial

section kth_power

variables {R : Type*} [semiring R] (p : polynomial R) {n : ℕ}

/-- the `k`th smallest exponent of p -/
def kth_power (h : p.support.card = n) : fin n ↪o ℕ :=
p.support.order_emb_of_fin h

lemma kth_power_mem_support (h : p.support.card = n) (k : fin n) : p.kth_power h k ∈ p.support :=
p.support.order_emb_of_fin_mem h k

lemma mem_support_iff_exists_kth_power (h : p.support.card = n) (j : ℕ) :
  j ∈ p.support ↔ ∃ k, p.kth_power h k = j :=
(set.ext_iff.mp (p.support.range_order_emb_of_fin h) j).symm

end kth_power

--TODO: move
lemma eval_sum' {R : Type*} [semiring R] {ι : Type*} (s : finset ι) (p : ι → polynomial R) (x : R) :
  eval x (∑ j in s, p j) = ∑ j in s, eval x (p j) :=
begin
  classical,
  apply finset.induction_on s,
  { rw [finset.sum_empty, finset.sum_empty, eval_zero] },
  { intros j s hj hpj,
    have h0 : ∑ i in insert j s, eval x (p i) = (eval x (p j)) + ∑ i in s, eval x (p i),
    { exact finset.sum_insert hj },
    rw [h0, ← hpj, finset.sum_insert hj, eval_add] },
end

structure n_omial (R : Type*) (n : ℕ) [semiring R] :=
(coeffs : fin n → R)
(powers : fin n ↪o ℕ)
(h_coeffs : ∀ i, coeffs i ≠ 0)

namespace n_omial

variables {R : Type*} [semiring R] {n : ℕ} (p : polynomial R) (t : n_omial R n)

@[ext] lemma ext {n : ℕ} {s t : n_omial R n} (hc : s.coeffs = t.coeffs)
  (hp : s.powers = t.powers) : s = t :=
begin
  cases s,
  cases t,
  exact mk.inj_eq.mpr ⟨hc, hp⟩,
end

/-- unbundle an n_omial -/
noncomputable def to_polynomial : polynomial R :=
∑ (k : fin n), monomial (t.powers k) (t.coeffs k)

/-- bundle an n_omial -/
def of_polynomial {p : polynomial R} (h : p.support.card = n) : n_omial R n :=
{ coeffs := λ k, p.coeff (p.kth_power h k),
  powers := p.kth_power h,
  h_coeffs := λ k, mem_support_iff_coeff_ne_zero.mp (p.kth_power_mem_support h k) }

lemma of_polynomial_to_polynomial {p : polynomial R} (h : p.support.card = n) :
  (of_polynomial h).to_polynomial = p :=
begin
  rw [to_polynomial, finset.sum_bij (λ k _, p.kth_power h k)],
  { exact p.as_sum_support.symm },
  { exact λ k _, p.kth_power_mem_support h k },
  { exact λ k _, rfl },
  { exact λ i j _ _ hij, (p.kth_power h).injective hij },
  { intros j hj,
    obtain ⟨k, hk⟩ := (p.mem_support_iff_exists_kth_power h j).mp hj,
    refine ⟨k, finset.mem_univ k, hk.symm⟩, },
end

lemma coeff_to_polynomial (k : fin n) : t.to_polynomial.coeff (t.powers k) = t.coeffs k :=
begin
  rw [to_polynomial, finset_sum_coeff],
  refine (finset.sum_eq_single k _ _).trans _,
  { intros b h1 h2,
    rw [coeff_monomial, if_neg (λ h, h2 (t.powers.injective h))] },
  { exact λ h, false.elim (h (finset.mem_univ k)) },
  { rw [coeff_monomial, if_pos rfl] },
end

lemma support_to_polynomial : t.to_polynomial.support = finset.image t.powers finset.univ :=
begin
  apply finset.subset.antisymm,
  { intros x hx,
    rw finset.mem_image,
    rw [mem_support_iff_coeff_ne_zero, to_polynomial, finset_sum_coeff] at hx,
    contrapose! hx,
    exact finset.sum_eq_zero (λ k hk, by rw [coeff_monomial, if_neg (hx k hk)]) },
  { intros x hx,
    obtain ⟨a, b, rfl⟩ := finset.mem_image.mp hx,
    rw [mem_support_iff_coeff_ne_zero, coeff_to_polynomial],
    exact t.h_coeffs a },
end

lemma card_support_to_polynomial : t.to_polynomial.support.card = n :=
begin
  rw [support_to_polynomial, finset.card_image_of_inj_on, finset.card_fin],
  exact λ _ _ _ _ h, t.powers.injective h,
end

lemma to_polynomial_of_polynomial : of_polynomial t.card_support_to_polynomial = t :=
begin
  suffices : (of_polynomial t.card_support_to_polynomial).powers = t.powers,
  { refine ext (funext (λ k, _)) this,
    rw [←t.coeff_to_polynomial k, ←this],
    refl },
  refine (finset.order_emb_of_fin_unique' _ $ λ x, _).symm,
  rw [t.support_to_polynomial, finset.mem_image],
  exact ⟨_, finset.mem_univ _, rfl⟩,
end

noncomputable def to_polynomial_equiv : n_omial R n ≃ {p : polynomial R // p.support.card = n} :=
{ to_fun := λ pn, ⟨pn.to_polynomial, pn.card_support_to_polynomial⟩,
  inv_fun := λ p, of_polynomial p.prop,
  left_inv := λ pn, to_polynomial_of_polynomial _,
  right_inv := λ pn, subtype.ext $ of_polynomial_to_polynomial _ }

lemma to_polynomial_injective : function.injective (to_polynomial : n_omial R n → polynomial R) :=
subtype.val_injective.comp to_polynomial_equiv.injective

lemma to_polynomial_inj {s t : n_omial R n} :
  s.to_polynomial = t.to_polynomial ↔ s = t :=
to_polynomial_injective.eq_iff

lemma to_polynomial_eq_zero : t.to_polynomial = 0 ↔ n = 0 :=
by rw [←finsupp.card_support_eq_zero, card_support_to_polynomial]

lemma eval_one_to_polynomial : t.to_polynomial.eval 1 = ∑ (k : fin n), t.coeffs k :=
by simp_rw [to_polynomial, eval_sum', eval_monomial, one_pow, mul_one]

lemma support_card_eq_n_iff :
  p.support.card = n ↔ ∃ t : n_omial R n, p = t.to_polynomial :=
begin
  split,
  { exact λ h, ⟨of_polynomial h, (of_polynomial_to_polynomial h).symm⟩ },
  { rintros ⟨t, rfl⟩,
    exact t.card_support_to_polynomial },
end

/-- twist a trinomial by a unit -/
def twist (u : units R) : n_omial R n :=
{ coeffs := λ k, u * (t.coeffs k),
  powers := t.powers,
  h_coeffs := λ k, mt u.mul_right_eq_zero.mp (t.h_coeffs k) }

lemma twist_one : t.twist 1 = t :=
ext (one_mul t.coeffs) rfl

lemma twist_twist (u v : units R) : (t.twist v).twist u = t.twist (u * v) :=
ext (mul_assoc _ _ t.coeffs).symm rfl

instance : mul_action (units R) (n_omial R n) :=
{ smul := λ u t, t.twist u,
  one_smul := twist_one,
  mul_smul := λ u v t, (t.twist_twist u v).symm }

lemma smul_to_polynomial (u : units R) : (u • t).to_polynomial = (u : R) • t.to_polynomial :=
by { simp_rw [to_polynomial, finset.smul_sum, smul_monomial], refl }

lemma neg_to_polynomial {R : Type*} [ring R] (t : n_omial R n) :
  ((-1 : units R) • t).to_polynomial = -t.to_polynomial :=
by rw [smul_to_polynomial, units.coe_neg_one, ←C_mul', C_neg, C_1, neg_one_mul]

lemma neg_neg {R : Type*} [ring R] (t : n_omial R n) : (-1 : units R) • (-1 : units R) • t = t :=
by rw [smul_smul, units.neg_mul_neg, one_mul, one_smul]

/-- reverse a trinomial -/
def reverse : n_omial R n :=
{ coeffs := λ k, (list.of_fn t.coeffs).reverse.nth_le k (by { sorry  }),
  powers := sorry,
  h_coeffs := sorry, }

lemma reverse_smul (u : units R) : (u • t).reverse = u • t.reverse := sorry

lemma reverse_to_polynomial : t.reverse.to_polynomial = t.to_polynomial.reverse' :=
begin
  rw [reverse', t.nat_trailing_degree, polynomial.reverse, t.nat_degree],
  simp_rw [to_polynomial, reflect_add, ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow,
    C_mul_X_pow_eq_monomial, X_pow_eq_monomial t.i, add_mul, monomial_mul_monomial, mul_one],
  rw [rev_at_le (le_of_lt t.hik), nat.sub_add_cancel (le_of_lt t.hik)],
  rw [rev_at_le (le_of_lt t.hjk), nat.sub_add_eq_add_sub (le_of_lt t.hjk), nat.add_comm t.k t.i],
  rw [rev_at_le (le_refl t.k), nat.sub_self, zero_add],
  rw [add_assoc (monomial t.k t.a), add_comm (monomial t.k t.a), add_comm _ (monomial t.i t.c)],
  refl,
end

lemma reverse_reverse : t.reverse.reverse = t :=
by rw [←to_polynomial_inj, reverse_to_polynomial, reverse_to_polynomial, reverse'_reverse'/

section main_proof

section rel

variables {S : Type*} [ring S] (q r s : n_omial S 3)

/-- two trinomial are related if they are the same up to negation and reverse -/
def rel :=
s = r ∨ s = (-1 : units S) • r ∨ s = r.reverse ∨ s = (-1 : units S) • r.reverse

@[refl] lemma rel_refl : rel s s := or.inl rfl

lemma rel_of_neg_rel : rel ((-1 : units S) • r) s → rel r s :=
begin
  rintro (h | h | h | h),
  { exact or.inr (or.inl h) },
  { exact or.inl (by rw [h, neg_neg]) },
  { exact or.inr (or.inr (or.inr (by rw [h, reverse_smul]))) },
  { exact or.inr (or.inr (or.inl (by rw [h, reverse_smul, neg_neg]))) },
end

lemma neg_rel : rel ((-1 : units S) • r) s ↔ rel r s :=
begin
  split,
  { exact rel_of_neg_rel r s },
  { exact λ h, rel_of_neg_rel ((-1 : units S) • r) s (by rwa neg_neg) },
end

lemma rel_of_reverse_rel : rel r.reverse s → rel r s :=
begin
  rintro (h | h | h | h),
  { exact or.inr (or.inr (or.inl h)) },
  { exact or.inr (or.inr (or.inr h)) },
  { exact or.inl (h.trans r.reverse_reverse) },
  { exact or.inr (or.inl (h.trans (congr_arg _ r.reverse_reverse))) },
end

lemma reverse_rel : rel r.reverse s ↔ rel r s :=
begin
  split,
  { exact rel_of_reverse_rel r s },
  { exact λ h, rel_of_reverse_rel r.reverse s (by rwa r.reverse_reverse) },
end

@[symm] lemma rel_symm : rel r s → rel s r :=
begin
  rintro (h | h | h | h),
  all_goals { simp only [h, neg_rel, reverse_rel] },
end

@[trans] lemma rel_trans : rel q r → rel r s → rel q s :=
begin
  rintros (h | h | h | h),
  all_goals { simp only [h, neg_rel, reverse_rel], exact id },
end

lemma rel_comm : rel r s ↔ rel s r := ⟨rel_symm r s, rel_symm s r⟩

lemma rel_neg : rel r ((-1 : units S) • s) ↔ rel r s :=
by rw [rel_comm, neg_rel, rel_comm]

lemma rel_reverse : rel r s.reverse ↔ rel r s :=
by rw [rel_comm, reverse_rel, rel_comm]

lemma unit_rel (r s : trinomial ℤ) (u : units ℤ) : rel (u • r) s ↔ rel r s :=
begin
  cases int.units_eq_one_or u with hu hu,
  { rw [hu, one_smul] },
  { rw [hu, neg_rel] },
end

lemma rel_unit (r s : trinomial ℤ) (u : units ℤ) : rel r (u • s) ↔ rel r s :=
begin
  cases int.units_eq_one_or u with hu hu,
  { rw [hu, one_smul] },
  { rw [hu, rel_neg] },
end

end rel

lemma monomial_add_monomial_eq_monomial_add_monomial_iff {R : Type*} [ring R]
  {a b : R} (ha : a ≠ 0) (hb : b ≠ 0) {i j k l : ℕ} :
  (monomial i a) + (monomial j b) = (monomial k a) + (monomial l b) ↔
  ((i = k ∧ j = l) ∨ (a = b ∧ i = l ∧ j = k) ∨ (a + b = 0 ∧ i = j ∧ k = l)) :=
begin
  split,
  { intro h,
    by_cases hjl : j = l,
    { exact or.inl ⟨by rwa [hjl, add_left_inj, monomial_left_inj ha] at h, hjl⟩ },
    { have key := congr_arg (λ x : polynomial R, x.coeff l) h,
      simp_rw [coeff_add, coeff_monomial, if_pos rfl, if_neg hjl, add_zero] at key,
      by_cases hil : i = l,
      { by_cases hkl : k = l,
        { rw [if_pos hil, if_pos hkl, self_eq_add_right] at key,
          exact false.elim (hb key) },
        { rw [if_pos hil, if_neg hkl, zero_add] at key,
          rw [key, hil, add_comm, add_left_inj, monomial_left_inj hb] at h,
          exact or.inr (or.inl ⟨key, hil, h⟩) } },
      { by_cases hkl : k = l,
        { rw [if_neg hil, if_pos hkl, eq_comm] at key,
          rw [hkl, ←monomial_add, key, monomial_zero_right, add_eq_zero_iff_eq_neg,
              ←monomial_neg, ←add_eq_zero_iff_eq_neg.mp key, monomial_left_inj ha] at h,
          exact or.inr (or.inr ⟨key, h, hkl⟩) },
        { rw [if_neg hil, if_neg hkl, zero_add, eq_comm] at key,
          exact false.elim (hb key) } } } },
  { rintros (⟨hik, hkl⟩ | ⟨hab, hil, hjk⟩ | ⟨hab, hij, hkl⟩),
    { rw [hik, hkl] },
    { rw [hab, hil, hjk, add_comm] },
    { rw [hij, hkl, ←monomial_add, ←monomial_add, hab,
          monomial_zero_right, monomial_zero_right] } },
end

lemma mul_reverse'_filter {R : Type*} [integral_domain R] (p : trinomial R) :
  (p.to_polynomial * p.to_polynomial.reverse').filter (set.Ioo (p.k + p.i) (p.k + p.k)) =
    (monomial (p.k + (p.k + p.i - p.j)) (p.b * p.c)) + (monomial (p.k + p.j) (p.b * p.a)) :=
begin
  rw [←reverse_to_polynomial, reverse, to_polynomial, to_polynomial],
  simp_rw [mul_add, add_mul, monomial_mul_monomial, monomial_def, finsupp.filter_add, ←add_assoc],
  rw [mul_comm p.c p.b, add_comm p.i p.k, add_comm p.j p.k, add_comm p.i (p.k + p.i - p.j)],
  rw [finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_neg,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_neg, finsupp.filter_single_of_pos,
      finsupp.filter_single_of_neg, finsupp.filter_single_of_pos, finsupp.filter_single_of_neg],
  simp_rw [zero_add, add_zero],
  { exact not_and_of_not_right _ (lt_irrefl _) },
  { exact ⟨add_lt_add_left p.hij p.k, add_lt_add_left p.hjk p.k⟩ },
  { exact not_and_of_not_left _ (lt_irrefl _) },
  { exact ⟨add_lt_add_left (nat.lt_sub_left_iff_add_lt.mpr (add_lt_add_right p.hjk p.i)) p.k,
      add_lt_add_left ((nat.sub_lt_right_iff_lt_add ((le_of_lt p.hjk).trans
      (nat.le_add_right _ _))).mpr (add_lt_add_left p.hij p.k)) p.k⟩ },
  { exact not_and_of_not_left _ (not_lt_of_le (le_of_eq
      (nat.add_sub_cancel' ((le_of_lt p.hjk).trans (nat.le_add_right _ _))))) },
  { exact not_and_of_not_left _ (not_lt_of_le (add_le_add_right
      (nat.sub_le_right_iff_le_add.mpr (add_le_add_left (le_of_lt p.hij) _)) _)) },
  { exact not_and_of_not_left _ (lt_irrefl _) },
  { exact not_and_of_not_left _ (not_lt_of_gt (add_lt_add_right p.hjk p.i)) },
  { exact not_and_of_not_left _ (not_lt_of_gt (add_lt_add_right p.hik p.i)) },
end

lemma key_lemma_aux2 {R : Type*} [integral_domain R] (p q : trinomial R) (hpqa : p.a = q.a)
  (hpqb : p.b = q.b) (hpqc : p.c = q.c)
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have hpqi : p.i = q.i,
  { replace hpq := congr_arg polynomial.nat_trailing_degree hpq,
    rw [nat_trailing_degree_mul_reverse', nat_trailing_degree_mul_reverse',
        nat_trailing_degree, nat_trailing_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  have hpqk : p.k = q.k,
  { replace hpq := congr_arg polynomial.nat_degree hpq,
    rw [nat_degree_mul_reverse', nat_degree_mul_reverse', nat_degree, nat_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  have key : (monomial (p.k + (p.k + p.i - p.j)) (p.b * p.c)) + (monomial (p.k + p.j) (p.b * p.a))
    = (monomial (q.k + (q.k + q.i - q.j)) (q.b * q.c)) + (monomial (q.k + q.j) (q.b * q.a)),
  { rw [←mul_reverse'_filter, ←mul_reverse'_filter, hpq, hpqi, hpqk] },
  rw [hpqa, hpqb, hpqc, hpqi, hpqk, monomial_add_monomial_eq_monomial_add_monomial_iff
      (mul_ne_zero q.hb q.hc) (mul_ne_zero q.hb q.ha)] at key,
  simp_rw add_right_inj at key,
  rcases key with (⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩),
  { exact or.inl (ext hpqa hpqb hpqc hpqi h2 hpqk).symm },
  { rw [mul_right_inj' q.hb] at h1,
    rw [add_comm, ←hpqi, ←hpqk] at h2,
    exact or.inr (or.inr (or.inl (eq.symm
      (ext (hpqc.trans h1) hpqb (hpqa.trans h1.symm) hpqi h2 hpqk)))) },
  { rw [nat.sub_eq_iff_eq_add ((le_of_lt q.hjk).trans (nat.le_add_right _ _)), ←two_mul] at h3,
    rw [nat.sub_eq_iff_eq_add, ←two_mul, h3, nat.mul_right_inj zero_lt_two, eq_comm] at h2,
    exact or.inl (ext hpqa hpqb hpqc hpqi h2 hpqk).symm,
    exact (le_of_lt p.hjk).trans ((le_of_eq hpqk).trans (nat.le_add_right _ _)) },
end

/- I don't expect anyone to want to use this lemma in positive characteristic, but this lemma
  does generalize to odd characteristic (with the same proof) -/
lemma key_lemma_aux1 {R : Type*} [integral_domain R] [char_zero R]
  (p q : trinomial R) (hpqa : p.a = q.a)
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have hpqc : p.c = q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [hpqa, mul_eq_mul_right_iff, or_iff_not_imp_right, imp_iff_right q.ha] at hpq },
  have key1 : p.to_polynomial.norm2 = q.to_polynomial.norm2,
  { rw [←central_coeff_mul_reverse', hpq, central_coeff_mul_reverse'] },
  rw [p.norm2, q.norm2, hpqa, hpqc, add_left_inj, add_right_inj] at key1,
  cases eq_or_eq_neg_of_pow_two_eq_pow_two _ _ key1 with hpqb hpqb,
  { exact key_lemma_aux2 p q hpqa hpqb hpqc hpq },
  have key2 := congr_arg (eval 1) hpq,
  rw [eval_mul, eval_mul, reverse'_eval_one, reverse'_eval_one, ←pow_two, ←pow_two,
    p.eval_one, q.eval_one, hpqa, hpqc] at key2,
  cases eq_or_eq_neg_of_pow_two_eq_pow_two _ _ key2 with hpqb hqac,
  { rw [add_left_inj, add_right_inj] at hpqb,
    exact key_lemma_aux2 p q hpqa hpqb hpqc hpq },
  { rw [add_comm q.a, add_comm q.a, add_assoc, add_assoc, neg_add, hpqb, add_right_inj,
        eq_neg_iff_add_eq_zero, add_self_eq_zero] at hqac,
    rw [←rel_reverse, ←rel_neg],
    apply key_lemma_aux2,
    { exact hpqa.trans ((add_eq_zero_iff_eq_neg.mp hqac).trans (neg_one_mul q.c).symm) },
    { exact hpqb.trans (neg_one_mul q.b).symm },
    { exact hpqc.trans ((neg_one_mul q.a).trans (add_eq_zero_iff_neg_eq.mp hqac)).symm },
    { rw [neg_to_polynomial, reverse'_neg, neg_mul_neg, reverse_to_polynomial, reverse'_reverse',
          hpq, mul_comm] } },
end

lemma key_lemma {p q : trinomial ℤ}
  (hp : is_unit (p.a * p.c) ∨ irreducible (p.a * p.c))
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  rel p q :=
begin
  have h := @algebra.smul_mul_smul _ _ _ _ (@polynomial.algebra_of_algebra ℤ ℤ _ _ (algebra.id ℤ)),
  have hp' : ∀ x y, p.a * p.c = x * y → is_unit x ∨ is_unit y := or.elim hp (λ h1 x y h2, or.inl
    (is_unit_of_mul_is_unit_left ((congr_arg is_unit h2).mp h1))) irreducible.is_unit_or_is_unit,
  have key : p.a * p.c = q.a * q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [mul_comm p.a p.c, mul_comm q.a q.c] },
  rcases (hp' p.a p.c rfl) with ⟨u1, hu1⟩ | ⟨u1, hu1⟩,
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { have key' := key_lemma_aux1 (u1 • p.reverse) (u2 • q.reverse)
        (by rwa [←hu1, ←hu2] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, reverse_rel, rel_reverse] at key' },
    { have key' := key_lemma_aux1 (u1 • p.reverse) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, reverse_rel] at key' } },
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { have key' := key_lemma_aux1 (u1 • p) (u2 • q.reverse)
        (by rwa [←hu1, ←hu2, mul_comm p.a] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          h, int.units_coe_mul_self, mul_comm, hpq]),
      rwa [unit_rel, rel_unit, rel_reverse] at key' },
    { have key' := key_lemma_aux1 (u1 • p) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm p.a, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse'_smul,
          h, int.units_coe_mul_self, hpq]),
      rwa [unit_rel, rel_unit] at key' } },
end

lemma reverse'_irreducible_test' {f : polynomial ℤ}
  (h1 : f.norm2 = 3)
  (h2 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  obtain ⟨t, rfl⟩ := support_card_eq_three_iff.mp
    (f.card_support_eq_three_of_norm2_eq_three h1),
  refine reverse'_irreducible_test (λ h3, _) _ h2,
  { obtain ⟨r, ⟨u, rfl⟩, h4⟩ := is_unit_iff.mp h3,
    rw [←h4, norm2_C, ←units.coe_pow, int.units_pow_two, units.coe_one] at h1,
    exact ne_of_lt (int.add_lt_add zero_lt_one one_lt_two) h1 },
  { intros g hg,
    have hg' : g.norm2 = 3,
    { rwa [←central_coeff_mul_reverse', ←hg, central_coeff_mul_reverse'] },
    obtain ⟨s, rfl⟩ := support_card_eq_three_iff.mp
      (g.card_support_eq_three_of_norm2_eq_three hg'),
    simp_rw [←reverse_to_polynomial, ←neg_to_polynomial, to_polynomial_inj],
    refine rel_symm s t (key_lemma _ hg.symm),
    apply or.inl,
    have key1 := s.to_polynomial.coeff_sq_eq_one_of_norm2_le_three (le_of_eq hg') s.i,
    have key2 := s.to_polynomial.coeff_sq_eq_one_of_norm2_le_three (le_of_eq hg') s.k,
    rw [s.coeff_i, pow_two] at key1,
    rw [s.coeff_k, pow_two] at key2,
    exact is_unit.mul (is_unit_of_mul_eq_one s.a s.a (key1 s.ha))
      (is_unit_of_mul_eq_one s.c s.c (key2 s.hc)) },
end

lemma reverse'_irreducible_test'' {f : polynomial ℤ}
  (h1 : f.norm2 = 3)
  (h2 : ∀ z : ℂ, ¬ (aeval z f = 0 ∧ aeval z f.reverse' = 0)) : irreducible f :=
begin
  have hf : f ≠ 0,
  { rw [ne, ←norm2_eq_zero, h1],
    exact int.bit1_ne_zero 1 },
  apply reverse'_irreducible_test' h1,
  intros g hg1 hg2,
  suffices : ¬ (0 < g.nat_degree),
  { rw [not_lt, nat.le_zero_iff] at this,
    rw [eq_C_of_nat_degree_eq_zero this, is_unit_C, ←this],
    cases hg1 with h fgh,
    apply @is_unit_of_mul_is_unit_left _ _ g.leading_coeff h.leading_coeff,
    rw [←leading_coeff_mul, ←fgh],
    exact is_unit_of_pow_eq_one _ _ (f.coeff_sq_eq_one_of_norm2_le_three
      (le_of_eq h1) f.nat_degree (mt leading_coeff_eq_zero.mp hf)) zero_lt_two },
  intro h,
  have inj : function.injective (algebra_map ℤ ℂ) := int.cast_injective,
  rw [nat_degree_pos_iff_degree_pos, ←degree_map' inj] at h,
  cases complex.exists_root h with z hz,
  apply h2 z,
  rw [is_root, eval_map, ←aeval_def] at hz,
  split,
  { cases hg1 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  { cases hg2 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
end

lemma selmer_coprime_lemma (n : ℕ) (z : ℂ) : ¬ (z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) :=
begin
  rintros ⟨h1, h2⟩,
  rw h1 at h2,
  have h3 : (z - 1) * (z + 1 + z ^ 2) = 0,
  { rw [h2, mul_zero] },
  replace h3 : z ^ 3 = 1,
  { rw [←sub_eq_zero, ←h3],
    ring },
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2,
  { rw [←nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one],
    have : n % 3 < 3 := nat.mod_lt n zero_lt_three,
    interval_cases n % 3,
    all_goals { rw h },
    { exact or.inl (pow_zero z) },
    { exact or.inr (or.inl (pow_one z)) },
    { exact or.inr (or.inr rfl) } },
  have z_ne_zero : z ≠ 0,
  { intro h,
    rw [h, zero_pow (zero_lt_three)] at h3,
    exact zero_ne_one h3 },
  rcases key with key | key | key,
  { rw [key, self_eq_add_left] at h1,
    exact z_ne_zero h1 },
  { rw [key, self_eq_add_right] at h1,
    exact one_ne_zero h1 },
  { rw [←key, h1, add_self_eq_zero, ←h1] at h2,
    exact z_ne_zero (pow_eq_zero h2) },
end

lemma selmer_irreducible {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℤ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact irreducible_of_associated ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  let p := mk (-(1 : ℤ)) (-(1 : ℤ)) (1 : ℤ) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (one_ne_zero) 0 1 n zero_lt_one hn,
  have h1 : p.to_polynomial = X ^ n - X - 1,
  { simp_rw [to_polynomial, ←C_mul_X_pow_eq_monomial, C_neg, C_1],
    ring },
  have h2 : p.to_polynomial.reverse' = 1 - X ^ (n - 1) - X ^ n,
  { simp_rw [←reverse_to_polynomial, reverse, to_polynomial, ←C_mul_X_pow_eq_monomial,
      C_neg, C_1, nat.zero_add],
    ring },
  rw ← h1,
  apply reverse'_irreducible_test'' (by { rw p.norm2, norm_num }),
  rw [h2, h1],
  rintros z ⟨hz1, hz2⟩,
  rw [alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, aeval_X, aeval_one,
      sub_sub, sub_eq_zero] at hz1,
  rw [alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, alg_hom.map_pow,
      aeval_X, aeval_one, sub_sub, sub_eq_zero, hz1, ←add_assoc, self_eq_add_left] at hz2,
  replace hz2 : z ^ n + z ^ 2 = 0,
  { rw [←nat.sub_add_cancel (le_of_lt hn), pow_succ, pow_two, ←mul_add, hz2, mul_zero] },
  exact selmer_coprime_lemma n z ⟨hz1, hz2⟩,
end

lemma selmer_irreducible' {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℚ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact irreducible_of_associated ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  let p := mk (-(1 : ℤ)) (-(1 : ℤ)) (1 : ℤ) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (one_ne_zero) 0 1 n zero_lt_one hn,
  have hp : p.to_polynomial = X ^ n - X - 1,
  { simp_rw [to_polynomial, ←C_mul_X_pow_eq_monomial, C_neg, C_1],
    ring },
  have h := (is_primitive.int.irreducible_iff_irreducible_map_cast _).mp (selmer_irreducible hn1),
  { rwa [map_sub, map_sub, map_pow, map_one, map_X] at h },
  { rw ← hp,
    exact monic.is_primitive p.leading_coeff },
end

end main_proof

end n_omial

end polynomial
