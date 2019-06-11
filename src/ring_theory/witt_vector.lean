import data.list.basic
import data.set.finite
import data.nat.prime
import data.nat.choose
import data.int.gcd
import data.mv_polynomial
import algebra.group_power
import algebra.char_p
import group_theory.subgroup
import ring_theory.multiplicity
import ring_theory.unique_factorization_domain
import data.padics.padic_integers

import tactic.tidy
import tactic.omega
import tactic.explode

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this section should move to other files

section finset

variables {G : Type u} [comm_group G]
variables {H : Type v} [comm_group H]
variables (i : G → H) [is_group_hom i]
variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → G)

-- This is finset.sum_hom

@[to_additive is_add_group_hom.map_finset_sum]
lemma is_group_hom.map_finset_prod : i (s.prod f) = s.prod (i ∘ f) :=
begin
  apply finset.induction_on s,
  { exact is_group_hom.map_one i },
  { intros x s' hx ih,
    rw [finset.prod_insert hx, finset.prod_insert hx, is_group_hom.map_mul i, ←ih] }
end

lemma dvd_sum {α : Type*} {β : Type*} [decidable_eq α] [comm_ring β]
  (s : finset α) (f : α → β) (b : β) (H : ∀ a ∈ s, b ∣ f a) :
  b ∣ s.sum f :=
begin
  let t := s,
  replace H : ∀ a ∈ t, b ∣ f a := H,
  have hs : s ⊆ t := finset.subset.refl s,
  revert hs,
  apply finset.induction_on s, {simp},
  intros a s' ha IH hs',
  rw finset.insert_subset at hs',
  cases hs' with has hs',
  simp [*, dvd_add]
end

@[elim_cast] lemma coe_nat_dvd {α : Type*} [comm_ring α] (m n : ℕ) (h : m ∣ n) :
  (m : α) ∣ n :=
by { rcases h with ⟨k, rfl⟩, refine ⟨k, by norm_cast⟩ }

end finset

namespace mv_polynomial

open mv_polynomial finsupp

lemma eval₂_assoc {S : Type*} [decidable_eq S] [comm_ring S]
  {σ : Type*} [decidable_eq σ]
  {τ : Type*} [decidable_eq τ]
  {ι : Type*} [decidable_eq ι]
  (φ : σ → mv_polynomial ι S) (q : τ → mv_polynomial σ S)
  (p : mv_polynomial τ S) :
  eval₂ C (eval₂ C φ ∘ q) p = eval₂ C φ (eval₂ C q p) :=
by { rw eval₂_comp_left (eval₂ C φ), congr, funext, simp }

variables {R : Type*} {S : Type*} (f : R → S) {ι : Type*}
variables [decidable_eq R] [comm_ring R]
variables [decidable_eq S] [comm_ring S]
variables [is_ring_hom f] [decidable_eq ι]

lemma eval₂_sum' {X : Type*} [decidable_eq X] (s : finset X) (g : ι → S)
  (i : X → mv_polynomial ι R) :
  eval₂ f g (s.sum i) = s.sum (λ x, eval₂ f g $ i x) :=
begin
  apply finset.induction_on s,
  { simp },
  { intros x' s' hx' IH,
    simp [finset.sum_insert hx', IH] }
end

@[simp] lemma C_pow (r : R) (n : ℕ) :
  (C (r^n) : mv_polynomial ι R) = (C r)^n :=
by induction n; simp [pow_succ, *]

-- lemma eval₂_pow (g : ι → S) (p : mv_polynomial ι R) (n : ℕ) :
--   eval₂ f g (p^n) = (eval₂ f g p)^n :=
-- by induction n; simp [pow_succ, eval₂_mul, *]

end mv_polynomial

namespace modp
variables {α : Type*} [comm_ring α] {p : ℕ} (hp : nat.prime p)

notation x ` modᵢ ` I := (ideal.quotient.mk I x)
notation x ` modₛ ` s := (ideal.quotient.mk (ideal.span s) x)
notation x ` modₑ ` a := (ideal.quotient.mk (ideal.span ({a})) x)

lemma char_one.one_eq_zero [char_p α 1] : (1 : α) = 0 :=
by exact_mod_cast char_p.cast_eq_zero α 1

lemma char_one.elim [char_p α 1] (a b : α) : a = b :=
by rw [← one_mul a, ← one_mul b, char_one.one_eq_zero, zero_mul, zero_mul]

instance char_one_of_is_unit (h : is_unit (p : α)) :
  char_p (ideal.span ({p} : set α)).quotient 1 :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro hn, exact one_dvd n },
  { rintro ⟨c, rfl⟩,
    rw is_unit_iff_exists_inv at h,
    rcases h with ⟨b, hb⟩,
    rw [helper, nat.cast_mul, nat.cast_one, ← hb,
      ideal.quotient.eq_zero_iff_mem, mul_assoc],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩

include hp
instance (h : ¬ is_unit (p : α)) : char_p (ideal.span ({p} : set α)).quotient p :=
⟨begin
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({p} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({p} : set α)) (m : α),
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro H,
    rw [helper, ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton] at H,
    rcases H with ⟨c, hc⟩,
    cases nat.coprime_or_dvd_of_prime hp n with hn hn,
    swap, {exact hn},
    have key := nat.gcd_eq_gcd_ab p n,
    delta nat.coprime at hn, rw hn at key,
    replace key := congr_arg (λ k : ℤ, (k : α)) key,
    simp only [int.cast_coe_nat, int.cast_add, int.coe_nat_zero, int.cast_mul, int.cast_one,
      int.coe_nat_succ, zero_add, hc] at key,
    rw [mul_assoc, ← mul_add] at key,
    exfalso, apply h,
    rw is_unit_iff_exists_inv,
    exact ⟨_, key.symm⟩ },
  { rintro ⟨c, rfl⟩,
    apply eq_zero_of_zero_dvd,
    use p,
    rw [zero_mul, helper (p*c), ideal.quotient.eq_zero_iff_mem, nat.cast_mul],
    exact ideal.mul_mem_right _ (ideal.subset_span $ set.mem_singleton p) }
end⟩
.

example (a b : α) : ((a + b)^p modₑ (p : α)) = (a^p modₑ (p : α)) + (b^p modₑ (p : α)) :=
begin
  classical,
  by_cases H : is_unit (p : α),
  { haveI := modp.char_one_of_is_unit H, exact char_one.elim _ _ },
  { haveI := modp.char_p hp H, simpa using add_pow_char _ hp _ _, apply_instance }
end

end modp

section
open multiplicity

lemma integral_of_denom_eq_one (r : ℚ) (h : r.denom = 1) : (r.num : ℚ) = r :=
begin
  rw [← rat.cast_of_int, rat.num_denom r, h, ← rat.mk_nat_eq],
  norm_cast, delta rat.of_int rat.mk_nat, congr,
  simp only [nat.gcd_one_right, int.nat_abs, nat.div_one]
end

lemma pnat.eq_one_of_padic_val_eq_zero (n : ℕ+) (h : ∀ p, nat.prime p → padic_val_rat p n = 0) :
  n = 1 :=
begin
  by_contra H,
  let p := nat.min_fac n,
  have hn : (n : ℕ) ≠ 1 := λ oops, H $ subtype.val_injective oops,
  have hp : nat.prime p := nat.min_fac_prime hn,
  have key : p ∣ n := nat.min_fac_dvd n,
  specialize h p hp,
  rw [show (n : ℚ) = ((n : ℕ) : ℤ), by simp] at h,
  rw padic_val_rat.padic_val_rat_of_int _ hp.ne_one _ at h,
  swap, { norm_cast, intro oops, exact ne_of_lt n.pos oops.symm },
  { rw [← pow_one p, multiplicity.pow_dvd_iff_le_multiplicity] at key,
    rw_mod_cast ← enat.coe_inj at h,
    norm_cast at h,
    rw h at key,
    norm_cast at key,
    exact nat.not_lt_zero _ key }
end

lemma integral_of_padic_val_ge_zero (r : ℚ) (h : ∀ p, nat.prime p → padic_val_rat p r ≥ 0) :
  (r.num : ℚ) = r :=
begin
  by_cases H : r = 0,
  { subst r, refl },
  apply integral_of_denom_eq_one,
  suffices : (⟨r.denom, r.pos⟩ : ℕ+) = (1 : ℕ+),
  { exact congr_arg subtype.val this },
  apply pnat.eq_one_of_padic_val_eq_zero,
  intros p hp,
  suffices : padic_val_rat p (r.denom : ℤ) = 0, by exact_mod_cast this,
  have rdnz : (r.denom : ℤ) ≠ 0, by exact_mod_cast ne_of_gt r.3,
  rw padic_val_rat.padic_val_rat_of_int _ hp.ne_one rdnz,
  have key := h p hp,
  have : r ≠ 0 ∧ p ≠ 1 := ⟨H, hp.ne_one⟩,
  rw [padic_val_rat, dif_pos this] at key,
  delta ge at key,
  rw sub_nonneg at key,
  norm_cast at key,
  rw [enat.get_le_get, int.coe_nat_multiplicity, multiplicity_le_multiplicity_iff] at key,
  norm_cast at key,
  suffices : multiplicity p r.denom = 0,
  { norm_cast, rw ← enat.coe_inj, simpa using this },
  rw [← le_zero_iff_eq, ← not_lt, enat.pos_iff_one_le, ← enat.coe_one,
    ← pow_dvd_iff_le_multiplicity],
  intro oops, apply hp.ne_one,
  replace key := key 1 (by simpa using oops),
  rw ← int.dvd_nat_abs at key,
  norm_cast at key,
  rw [← pow_one p, ← nat.dvd_one],
  suffices : p^1 ∣ nat.gcd (int.nat_abs r.num) r.denom,
  { by simpa [nat.coprime.gcd_eq_one r.4] },
  apply nat.dvd_gcd key,
  simpa using oops
end

end

namespace pnat

instance : has_dvd ℕ+ :=
⟨λ a b, ∃ c, b = a * c⟩

lemma dvd_iff_coe_dvd (a b : ℕ+) :
  a ∣ b ↔ (a : ℕ) ∣ b :=
begin
  split,
  { rintros ⟨c, rfl⟩, refine ⟨c, mul_coe _ _⟩ },
  { rintros ⟨c, hc⟩,
    refine ⟨⟨c, _⟩, _⟩,
    { apply pos_of_mul_pos_left,
      { rw ← hc, exact b.2 },
      exact nat.zero_le _ },
    -- todo(jmc): provide ext for pnat
    cases a, cases b, congr, exact hc }
end

end pnat

-- ### end FOR_MATHLIB

-- proper start of this file

open mv_polynomial set

-- variables (s : set ℕ+)

-- def witt_vectors (α : Type u) := s → α

-- local notation `𝕎` := witt_vectors

-- namespace witt_vectors

-- instance : functor (𝕎 s) :=
-- { map := λ α β f v, f ∘ v,
--   map_const := λ α β a v, λ _, a }

-- instance : is_lawful_functor (𝕎 s) :=
-- { map_const_eq := λ α β, rfl,
--   id_map := λ α v, rfl,
--   comp_map := λ α β γ f g v, rfl }

-- end witt_vectors

-- def pnat.divisors (n : ℕ+) : set ℕ+ :=
-- {d | d ∣ n}

-- noncomputable instance pnat.divisors.fintype (n : ℕ+) : fintype n.divisors :=
-- finite.fintype $ finite_of_finite_image (subtype.val_injective) $ finite_subset (finite_le_nat n) $
-- by { rintros _ ⟨_, ⟨c, rfl⟩, rfl⟩, exact nat.le_mul_of_pos_right c.property }

-- def set.is_truncation_set (s : set ℕ+) : Prop :=
-- ∀ (n : ℕ+), n ∈ s → n.divisors ⊆ s

-- def fintype.sum {α : Type*} {β : Type*} (f : α → β) [s : fintype α] [add_comm_monoid β] :=
-- s.elems.sum f

-- variables {s} (α : Type u) [decidable_eq α] [comm_ring α]

-- noncomputable def witt_polynomial (hs : s.is_truncation_set) (n : s) :
--   mv_polynomial s α :=
-- fintype.sum (λ (d : (n : ℕ+).divisors),
--   let d_in_s : (d : ℕ+) ∈ s := hs n n.property d.property in
--   C d * (X ⟨d, d_in_s⟩)^((n : ℕ)/d))

-- noncomputable def witt_polynomial_aux (n : ℕ+) :
--   mv_polynomial ℕ+ α := fintype.sum (λ (d : n.divisors), C d * (X d)^((n : ℕ)/d))

-- lemma witt_polynomial_compat (hs : s.is_truncation_set) (n : s) :
--   rename subtype.val (witt_polynomial α hs n) = witt_polynomial_aux α n :=
-- begin
--   delta witt_polynomial witt_polynomial_aux fintype.sum,
--   rw ← finset.sum_hom (rename (subtype.val : s → ℕ+)),
--   work_on_goal 0 {
--     congr' 1, funext d,
--     rw [is_ring_hom.map_mul (rename (subtype.val : s → ℕ+)),
--         is_monoid_hom.map_pow (rename (subtype.val : s → ℕ+)),
--         rename_C, rename_X] },
--   { norm_cast },
--   all_goals {apply_instance}
-- end

-- -- We need integers to be invertible for the following definitions
-- def X_in_terms_of_W : ℕ+ → mv_polynomial ℕ+ ℚ
-- | n := (X n - (fintype.sum (λ d : n.divisors,
--   have _ := d.2, (C (d : ℚ) * (X_in_terms_of_W d)^((n : ℕ)/d))))) * C (1/(n : ℚ))


-- #exit

local attribute [class] nat.prime
variables (α : Type u) [decidable_eq α] [comm_ring α]
variables (p : ℕ) [nat.prime p]

lemma dvd_sub_pow_of_dvd_sub (a b : α) (h : (p : α) ∣ a - b) (k : ℕ) :
  (p^(k+1) : α) ∣ a^(p^k) - b^(p^k) :=
begin
  induction k with k ih, { simpa using h }, clear h,
  simp only [nat.succ_eq_add_one],
  rcases ih with ⟨c, hc⟩,
  rw sub_eq_iff_eq_add' at hc,
  replace hc := congr_arg (λ x, x^p) hc,
  dsimp only at hc,
  rw [← pow_mul, add_pow, finset.sum_range_succ, nat.choose_self, nat.cast_one, mul_one,
    nat.sub_self, pow_zero, mul_one] at hc,
  conv { congr, skip, rw [nat.pow_succ] },
  simp only [nat.pow_eq_pow] at hc,
  rw [hc, pow_mul, add_sub_cancel'], clear hc a,
  apply dvd_sum,
  intros i hi,
  rw finset.mem_range at hi,
  rw mul_pow,
  conv { congr, skip, congr, congr, skip, rw mul_comm },
  repeat { rw mul_assoc, apply dvd_mul_of_dvd_right }, clear c b,
  norm_cast,
  apply coe_nat_dvd,
  by_cases H : i = 0,
  { subst H,
    suffices : p ^ (k + 1 + 1) ∣ (p ^ (k + 1)) ^ p, by simpa,
    rw ← nat.pow_mul,
    apply nat.pow_dvd_pow,
    refine le_trans (add_le_add_left' $ le_add_left $ le_refl _ : k + 1 + 1 ≤ k + 1 + (k + 1)) _,
    refine le_trans (le_of_eq _) (nat.mul_le_mul_left (k+1) $ (nat.prime.ge_two ‹_› : 2 ≤ p)),
    rw mul_two },
  have i_pos := nat.pos_of_ne_zero H, clear H,
  rw nat.pow_succ,
  apply mul_dvd_mul,
  { generalize H : (p^(k+1)) = b,
    have := nat.sub_pos_of_lt hi,
    conv {congr, rw ← nat.pow_one b},
    apply nat.pow_dvd_pow,
    exact this },
  exact nat.prime.dvd_choose i_pos hi ‹_›
end

section
open multiplicity nat

lemma finite_nat_prime_iff (i : ℕ) :
  finite p i ↔ i > 0 :=
begin
  rw finite_nat_iff, split; intro h,
  { exact h.2 },
  { exact ⟨ne_of_gt (prime.gt_one ‹_›), h⟩ }
end

lemma finite_nat_choose_iff' (k i : ℕ) :
  finite p (choose (p^k) i) ↔ (i ≤ p^k) :=
begin
  rw finite_nat_iff, split; intro h,
  { by_contradiction H, cases h,
    simp only [not_le, choose_eq_zero_of_lt, not_lt_zero, *] at * },
  { split,
    { exact ne_of_gt (prime.gt_one ‹_›) },
    { exact choose_pos h } }
end

end

@[simp] lemma enat.get_coe (n : ℕ) (h : (n : enat).dom) : (n : enat).get h = n := rfl

lemma multiplicity_add_one_le (k n : ℕ) (hk : k ≠ 1) (hn : 0 < n) :
  (multiplicity k n) + 1 ≤ n :=
begin
  have : multiplicity.finite k n,
  { rw multiplicity.finite_nat_iff, split; assumption },
  rw ← @enat.get_le_get (multiplicity k n + 1) n ⟨this, trivial⟩ trivial,
  { rw [enat.get_coe, enat.get_add, enat.get_one],
    by_cases H : k ≤ 1,
    { have duh : 0 ≤ k := zero_le k,
      have foo : k < 1 := lt_of_le_of_ne H hk,
      have k0 : k = 0 := by linarith,
      subst k,
      rw show (multiplicity 0 n).get this = 0,
      { rw [← enat.coe_inj, enat.coe_get, enat.coe_zero],
        rw multiplicity.multiplicity_eq_zero_of_not_dvd,
        rintro ⟨m, rfl⟩,
        rw nat.zero_mul at hn,
        exact nat.not_lt_zero 0 hn },
      exact hn },
  rw not_le at H,
  show _ < n,
  refine lt_of_lt_of_le (nat.lt_pow_self H _) (nat.le_of_dvd hn _),
  have := @multiplicity.pow_dvd_of_le_multiplicity ℕ _ _ k n
    ((multiplicity k n).get this) (by rw enat.coe_get),
  simpa }
end

@[simp] lemma enat.nat_cast_eq_coe (n : ℕ) :
  (@coe nat enat (@coe_to_lift nat enat (@coe_base nat enat nat.cast_coe)) n) = n :=
by { induction n with n IH, {refl}, simp [nat.succ_eq_add_one, IH] }

@[simp] lemma nat.choose_comm (n k : ℕ) (h : k ≤ n) :
  nat.choose n (n - k) = nat.choose n k :=
begin
  rw nat.choose_eq_fact_div_fact (nat.sub_le n k),
  rw nat.choose_eq_fact_div_fact h,
  rw [mul_comm, nat.sub_sub_self h]
end

open mv_polynomial

variables {R : Type u} [decidable_eq R] [comm_ring R]

theorem range_sum_eq_fin_univ_sum {α} [add_comm_monoid α] (f : ℕ → α) (n) :
  (finset.range n).sum f = finset.univ.sum (λ i : fin n, f i.1) :=
show _ = @multiset.sum α _ ↑(list.map _ _),
by rw [list.map_pmap, list.pmap_eq_map]; refl

def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
(finset.range (n+1)).sum (λ i, (C p ^ i * X i ^ (p^(n-i))))

variables (R)
/- View a polynomial written in terms of basis of Witt polynomials
as a polynomial written in terms of the standard basis.-/
def from_W_to_X_basis : mv_polynomial ℕ R → mv_polynomial ℕ R :=
eval₂ C (witt_polynomial p)

instance from_W_to_X_basis.is_ring_hom : is_ring_hom (from_W_to_X_basis p R) :=
by delta from_W_to_X_basis; apply_instance

lemma witt_polynomial_zero : (witt_polynomial p 0 : mv_polynomial ℕ R) = X 0 :=
begin
  delta witt_polynomial,
  simp [finset.sum_range_succ, finset.range_zero, finset.sum_empty],
end

lemma from_W_to_X_basis_W_n (n) : from_W_to_X_basis p R (X n) = witt_polynomial p n :=
by simp [from_W_to_X_basis]

variables {R}

-- We need p to be invertible for the following definitions
def X_in_terms_of_W : ℕ → mv_polynomial ℕ ℚ
| n := (X n - (finset.sum finset.univ (λ i : fin n,
  have _ := i.2, (C p^i.val * (X_in_terms_of_W i.val)^(p^(n-i.val)))))) * C (1/p^n)

lemma X_in_terms_of_W_eq {n : ℕ} : X_in_terms_of_W p n =
    (X n - (finset.range n).sum (λ i, C p ^ i * X_in_terms_of_W p i ^ p ^ (n - i))) *
      C (1/p^n) :=
by rw [X_in_terms_of_W, range_sum_eq_fin_univ_sum]

/- View a polynomial written in terms of basis of Witt polynomials
as a polynomial written in terms of the standard basis.-/
def from_X_to_W_basis : mv_polynomial ℕ ℚ → mv_polynomial ℕ ℚ :=
eval₂ C (X_in_terms_of_W p)

instance from_X_to_W_basis.is_ring_hom : is_ring_hom (from_X_to_W_basis p) :=
by delta from_X_to_W_basis; apply_instance

lemma X_in_terms_of_W_zero : X_in_terms_of_W p 0 = witt_polynomial p 0 :=
begin
  rw X_in_terms_of_W_eq,
  rw finset.range_zero,
  rw finset.sum_empty,
  rw witt_polynomial_zero,
  simp
end

lemma X_in_terms_of_W_aux {n} : X_in_terms_of_W p n * C(p^n) =
  X n - (finset.range n).sum (λ i, (C p)^i * (X_in_terms_of_W p i)^p^(n-i)) :=
begin
  rw [X_in_terms_of_W_eq, mul_assoc, ← C_mul],
  convert mul_one _,
  rw one_div_eq_inv,
  apply rat.inv_mul_cancel,
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›))
end

section -- Kudos to Mario

theorem nat.semiring_hom_eq_cast {α} [ring α]
  (f : ℕ → α) [is_semiring_hom f] (n : ℕ) : f n = n :=
nat.eq_cast' _ (is_semiring_hom.map_one _) (λ _ _, is_semiring_hom.map_add f) _

theorem int.ring_hom_eq_cast {α} [ring α]
  (f : ℤ → α) [is_ring_hom f] (n : ℤ) : f n = n :=
int.eq_cast _ (is_ring_hom.map_one _) (λ _ _, is_ring_hom.map_add f) _

theorem rat.ring_hom_unique {α} [ring α]
  (f g : ℚ → α) [is_ring_hom f] [is_ring_hom g] (r : ℚ) : f r = g r :=
rat.num_denom_cases_on' r $ λ a b b0, begin
  rw [rat.mk_eq_div, int.cast_coe_nat],
  have b0' : (b:ℚ) ≠ 0 := nat.cast_ne_zero.2 b0,
  have : ∀ n : ℤ, f n = g n := λ n,
    (int.ring_hom_eq_cast (f ∘ int.cast) n).trans
    (int.ring_hom_eq_cast (g ∘ int.cast) n).symm,
  calc f (a * b⁻¹)
      = f a * f b⁻¹ * (g (b:ℤ) * g b⁻¹) : by rw [
    int.cast_coe_nat, ← is_ring_hom.map_mul g,
    mul_inv_cancel b0', is_ring_hom.map_one g, mul_one,
    is_ring_hom.map_mul f]
  ... = g a * f b⁻¹ * (f (b:ℤ) * g b⁻¹) : by rw [this a, ← this b]
  ... = g (a * b⁻¹) : by rw [
    int.cast_coe_nat, mul_assoc, ← mul_assoc (f b⁻¹),
    ← is_ring_hom.map_mul f, inv_mul_cancel b0',
    is_ring_hom.map_one f, one_mul,
    is_ring_hom.map_mul g]
end

end

lemma X_in_terms_of_W_prop'
  (f : mv_polynomial ℕ ℚ → mv_polynomial ℕ ℚ) [is_ring_hom f]
  (fX : ∀ (n : ℕ), f (X n) = @witt_polynomial p _ ℚ _ _ n)
  (n : ℕ) : f (X_in_terms_of_W p n) = X n :=
begin
  have fC : ∀ (a : ℚ), f (C a) = C a,
  { intro a, show (f ∘ C) a = _, apply rat.ring_hom_unique (f ∘ C) C a },
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [is_ring_hom.map_mul f, is_ring_hom.map_sub f, fC, fX, (finset.sum_hom f).symm],
  rw [finset.sum_congr rfl, (_ : @witt_polynomial p _ ℚ _ _ n -
    (finset.range n).sum (λ i, C p ^ i * X i ^ p ^ (n - i)) = C (p ^ n) * X n)],
  { rw [mul_right_comm, ← C_mul, mul_one_div_cancel, C_1, one_mul],
    exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›)) },
  { simp [witt_polynomial, nat.sub_self],
    rw finset.sum_range_succ,
    simp },
  { intros i h,
    rw finset.mem_range at h,
    simp only [is_ring_hom.map_mul f, is_semiring_hom.map_pow f, fC, function.comp_app],
    rw H _ h }
end

lemma from_W_to_X_basis_comp_from_X_to_W_basis (f) :
  from_W_to_X_basis p _ (from_X_to_W_basis p f) = f :=
begin
  show (from_W_to_X_basis p _ ∘ from_X_to_W_basis p) f = f,
  apply mv_polynomial.is_id,
  { apply_instance },
  { intro r,
    let : _ := _,
    refine @rat.ring_hom_unique _ _ _ _ this (by apply_instance) r,
    let F := (from_W_to_X_basis p _ ∘ from_X_to_W_basis p),
    change is_ring_hom (λ (r : ℚ), F (C r)),
    show is_ring_hom (F ∘ C),
    exact is_ring_hom.comp _ _ },
  { intro n,
    delta from_X_to_W_basis function.comp,
    erw eval₂_X,
    refine X_in_terms_of_W_prop' p _ _ n,
    intro k,
    erw from_W_to_X_basis_W_n p }
end

lemma X_in_terms_of_W_prop₂ (k : ℕ) : (witt_polynomial p k).eval₂ C (X_in_terms_of_W p) = X k :=
begin
  suffices : from_X_to_W_basis p ((C p)^k * X k) +
    from_X_to_W_basis p (finset.sum (finset.range k) (λ (i : ℕ), (C p)^i * (X i)^p^(k-i))) = X k,
  { simpa [witt_polynomial, finset.sum_range_succ] },
  suffices : ∀ i, from_X_to_W_basis p ((C p)^i * (X i)^p^(k-i)) =
    (C p)^i * (X_in_terms_of_W p i)^p^(k-i),
  { rw [is_ring_hom.map_mul (from_X_to_W_basis p),
        is_semiring_hom.map_pow (from_X_to_W_basis p),
        from_X_to_W_basis, eval₂_C, eval₂_X, X_in_terms_of_W_eq,
        mul_comm, mul_assoc, ← is_semiring_hom.map_pow C,
        ← C_mul, one_div_mul_cancel, C_1, mul_one,
        ← finset.sum_hom (eval₂ C $ X_in_terms_of_W p),
        sub_add_eq_add_sub, sub_eq_iff_eq_add],
    congr,
    funext i,
    exact this i,
    all_goals { try {apply_instance} },
    { refine pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt _),
      apply nat.prime.pos,
      assumption } },
  intro i,
  rw [is_ring_hom.map_mul (from_X_to_W_basis p),
      is_semiring_hom.map_pow (from_X_to_W_basis p),
      is_semiring_hom.map_pow (from_X_to_W_basis p),
      from_X_to_W_basis, eval₂_C, eval₂_X]
end

lemma X_in_terms_of_W_prop (n : ℕ) : (X_in_terms_of_W p n).eval₂ C (witt_polynomial p) = X n :=
begin
  change from_W_to_X_basis p ℚ _ = X n,
  apply X_in_terms_of_W_prop',
  intro n,
  apply from_W_to_X_basis_W_n,
end

lemma from_X_to_W_basis_comp_from_W_to_X_basis (f) :
  from_X_to_W_basis p (from_W_to_X_basis p _ f) = f :=
begin
  show (from_X_to_W_basis p ∘ from_W_to_X_basis p _) f = f,
  apply mv_polynomial.is_id,
  { apply_instance },
  { intro r,
    let : _ := _,
    refine @rat.ring_hom_unique _ _ _ _ this (by apply_instance) r,
    let F := (from_X_to_W_basis p ∘ from_W_to_X_basis p _),
    change is_ring_hom (λ (r : ℚ), F (C r)),
    show is_ring_hom (F ∘ C),
    exact is_ring_hom.comp _ _ },
  { intro n,
    delta from_W_to_X_basis function.comp,
    erw eval₂_X,
    delta from_X_to_W_basis,
    apply X_in_terms_of_W_prop₂ }
end

lemma from_X_to_W_basis_X_n (n) : from_X_to_W_basis p (witt_polynomial p n) = X n :=
by simp only [from_X_to_W_basis, eval₂_X, X_in_terms_of_W_prop₂]

def to_W_basis : mv_polynomial ℕ ℚ ≃r mv_polynomial ℕ ℚ :=
{ to_fun    := from_X_to_W_basis p,
  inv_fun   := from_W_to_X_basis p ℚ,
  left_inv  := λ _, from_W_to_X_basis_comp_from_X_to_W_basis _ _,
  right_inv := λ _, from_X_to_W_basis_comp_from_W_to_X_basis _ _,
  hom       := by apply_instance }

def witt_structure_rat (Φ : mv_polynomial bool ℚ) : ℕ → mv_polynomial (bool × ℕ) ℚ :=
λ n, eval₂ C (λ k : ℕ,
   Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (λ i, (b,i))))) (X_in_terms_of_W p n)

theorem witt_structure_prop (Φ : mv_polynomial bool ℚ) :
  ∃! (φ : ℕ → mv_polynomial (bool × ℕ) ℚ), ∀ (n : ℕ),
  (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : bool, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n,
    unfold witt_structure_rat,
    rw [← function.comp, eval₂_assoc, X_in_terms_of_W_prop₂ p n, eval₂_X] },
  { intros φ H,
    unfold witt_structure_rat,
    funext n,
    rw show φ n = ((X_in_terms_of_W p n).eval₂ C (witt_polynomial p)).eval₂ C φ,
    { rw [X_in_terms_of_W_prop p, eval₂_X] },
    rw ← eval₂_assoc,
    unfold function.comp,
    congr,
    funext k,
    exact H k },
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial bool ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n) =
  Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, (C p)^i * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  have := @X_in_terms_of_W_aux p _ n,
  replace := congr_arg (eval₂ C (λ k : ℕ,
  Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (λ i, (b,i)))))) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  conv_rhs { simp only [eval₂_sub, eval₂_X] },
  rw sub_left_inj,
  simp only [eval₂_sum'],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, ← C_pow, ← C_pow, eval₂_C, eval₂_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial bool ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n) *
  (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, (C p)^i * (witt_structure_rat p Φ i)^p^(n-i))) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, mul_comm, mul_assoc,
      ← C_mul, mul_one_div_cancel, C_1, mul_one],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›))
end

def witt_structure_int (Φ : mv_polynomial bool ℤ) (n : ℕ) : mv_polynomial (bool × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n)
.

section
variables {ι : Type*} [decidable_eq ι]

lemma coeff_X (i : ι) (m) (k : ℕ) :
  coeff m (X i ^ k : mv_polynomial ι R) = if finsupp.single i k = m then 1 else 0 :=
begin
  have := coeff_monomial m (finsupp.single i k) (1:R),
  rwa [@monomial_eq _ _ (1:R) (finsupp.single i k) _ _ _,
    C_1, one_mul, finsupp.prod_single_index] at this,
  exact pow_zero _
end

lemma mv_polynomial.ext_iff (p q : mv_polynomial ι α) :
(∀ m, coeff m p = coeff m q) ↔ p = q :=
⟨mv_polynomial.ext p q, λ h m, by rw h⟩

lemma nat.map_cast {α : Type*} {β : Type*} (f : α → β) [semiring α] [semiring β] [is_semiring_hom f]
  (n : ℕ) : f (n : α) = n :=
begin
  induction n with n ih, {rw_mod_cast is_add_monoid_hom.map_zero f},
  simp [is_semiring_hom.map_add f, is_semiring_hom.map_one f, ih]
end

variables {S : Type*} [decidable_eq S] [comm_ring S]

lemma map_witt_polynomial (f : R → S) [is_ring_hom f] (n) :
  map f (witt_polynomial p n) = witt_polynomial p n :=
begin
  apply mv_polynomial.ext,
  intro m,
  rw coeff_map,
  delta witt_polynomial,
  rw [← finset.sum_hom (coeff m), ← finset.sum_hom (coeff m), ← finset.sum_hom f],
  { apply finset.sum_congr rfl,
    intros i hi,
    repeat {rw [← C_pow, coeff_C_mul m, coeff_X]},
    rw is_ring_hom.map_mul f,
    split_ifs;
    [ rw is_ring_hom.map_one f, rw is_ring_hom.map_zero f ];
    simp only [mul_one, mul_zero],
    rw is_semiring_hom.map_pow f, congr,
    exact nat.map_cast f p },
  all_goals {apply_instance}
end

end

lemma mv_polynomial.coe_int_rat_map_injective (I : Type*) [decidable_eq I] :
  function.injective (map (coe : ℤ → ℚ) : mv_polynomial I ℤ → mv_polynomial I ℚ) :=
begin
  rw is_add_group_hom.injective_iff _,
  all_goals {try {apply_instance}},
  intros f hf,
  apply mv_polynomial.ext,
  intro m,
  rw ← mv_polynomial.ext_iff at hf,
  specialize hf m,
  rw [coeff_map, coeff_zero] at hf,
  rw coeff_zero,
  exact_mod_cast hf
end
.

lemma duh (a b c d : R) (h1 : a = c) (h2 : b = d) : a - b = c - d :=
by simp *
.

variables {ι : Type*} {σ : Type*} [decidable_eq ι] [decidable_eq σ]
variables {S : Type*} [decidable_eq S] [comm_ring S]
variables {T : Type*} [decidable_eq T] [comm_ring T]

#check eval₂_comp_left
-- k (eval₂ f g p) = eval₂ (k ∘ f) (k ∘ g) p

lemma eval₂_comp_right (f' : S → T) [is_ring_hom f'] (f : R → S) [is_ring_hom f]
  (g : σ → S) (p : mv_polynomial σ R) :
  f' (eval₂ f g p) = eval₂ f' (f' ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, is_ring_hom.map_add f', map_add, eval₂_add, hp, hq] },
  { intros p s hp,
    rw [eval₂_mul, is_ring_hom.map_mul f', map_mul, eval₂_mul, map_X, hp, eval₂_X, eval₂_X] }
end

lemma map_eval₂ (f : R → S) [is_ring_hom f] (g : σ → mv_polynomial ι R) (p : mv_polynomial σ R) :
  map f (eval₂ C g p) = eval₂ C (map f ∘ g) (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [eval₂_C, map_C, map_C, eval₂_C] },
  { intros p q hp hq, rw [eval₂_add, map_add, hp, hq, map_add, eval₂_add] },
  { intros p s hp,
    rw [eval₂_mul, map_mul, hp, map_mul, map_X, eval₂_mul, eval₂_X, eval₂_X] }
end
.

lemma map_rename (f : R → S) [is_ring_hom f] (g : σ → ι) (p : mv_polynomial σ R) :
  map f (rename g p) = rename g (map f p) :=
begin
  apply mv_polynomial.induction_on p,
  { intro r, rw [map_C, rename_C, map_C, rename_C] },
  { intros p q hp hq,
    rw [is_ring_hom.map_add (rename g), map_add, hp, hq, map_add, is_ring_hom.map_add (rename g)],
    all_goals {apply_instance} },
  { intros p s hp,
    rw [is_ring_hom.map_mul (rename g), map_mul, hp, map_mul, map_X,
        is_ring_hom.map_mul (rename g), rename_X, map_X, rename_X],
    all_goals {apply_instance} }
end
.

lemma foo (Φ : mv_polynomial bool ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < n → map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  map (coe : ℤ → ℚ) (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, (C p)^i * (witt_structure_int p Φ i)^p^(n-i))) =
  ((map coe Φ).eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) -
  (finset.range n).sum (λ i, (C p)^i * (witt_structure_rat p (map coe Φ) i)^p^(n-i))) :=
begin
  rw [is_ring_hom.map_sub (map (coe : ℤ → ℚ)), ← finset.sum_hom (map (coe : ℤ → ℚ))],
  all_goals {try {apply_instance}},
  work_on_goal 1 { exact @is_add_group_hom.to_is_add_monoid_hom _ _ _ _ _ _ },
  apply duh,
  { rw map_eval₂, congr' 1, funext b, dsimp, rw map_rename,
    erw map_witt_polynomial,
    refl },
  apply finset.sum_congr rfl,
  intros i hi,
  rw finset.mem_range at hi,
  specialize IH i hi,
  rw [is_ring_hom.map_mul (map (coe : ℤ → ℚ)),
      is_monoid_hom.map_pow (map (coe : ℤ → ℚ)),
      is_monoid_hom.map_pow (map (coe : ℤ → ℚ)),
      IH, map_C],
  work_on_goal 0 { congr },
  all_goals {try {apply_instance}},
  all_goals { refine @is_semiring_hom.is_monoid_hom _ _ _ _ _ _ },
end
.

def doh {α : Type*} [comm_ring α] : add_comm_monoid α := by apply_instance
def dah {α : Type*} [comm_ring α] : add_monoid α := by apply_instance

lemma quux (n : ℕ) :
  ((witt_polynomial p (n + 1) : mv_polynomial ℕ ℤ) modₑ (p : mv_polynomial ℕ ℤ)) =
  ((eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n)) modₑ (p : mv_polynomial ℕ ℤ)) :=
begin
  delta witt_polynomial,
  rw [← finset.sum_hom (ideal.quotient.mk _),
      ← finset.sum_hom (eval₂ C (λ (i : ℕ), X i ^ p)),
      ← finset.sum_hom (ideal.quotient.mk _),
      finset.sum_range_succ],
  all_goals {try { apply doh }},
  work_on_goal 0 {
    convert zero_add _ using 1,
    work_on_goal 1 { apply dah },
    congr' 1,
    work_on_goal 0 {
      apply ideal.quotient.eq_zero_iff_mem.mpr,
      rw [pow_succ, mul_assoc],
      apply ideal.mul_mem_right _ _,
      apply ideal.subset_span,
      rw mem_singleton_iff,
      clear _inst_3,
      induction p with n IH, { simp },
      rw [nat.succ_eq_add_one],
      rw [nat.cast_add, C_add, nat.cast_one, C_1, IH],
      refl },
    apply finset.sum_congr rfl,
    intros i hi,
    induction i with i _,
    { simp only [nat.nat_zero_eq_zero, one_mul, ideal.quotient.mk_pow,
        nat.sub_zero, int.nat_cast_eq_coe_nat, pow_zero],
      rw [eval₂_pow, eval₂_X, ← pow_mul, nat.pow_succ, mul_comm],
      simp },
    { rw [nat.succ_eq_add_one],


    }
  }
  -- all_goals { try {apply_instance} },

end

lemma bar (Φ : mv_polynomial bool ℤ) (n : ℕ) :
  map (coe : ℤ → ℚ) (witt_structure_int p Φ n) = witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  rw witt_structure_rat_rec p _ n,
  rw ← foo p Φ n IH,
  sorry
end
.

-- def has_integral_coeffs {ι : Type*} [decidable_eq ι] (p : mv_polynomial ι ℚ) : Prop :=
--   ∀ m, (coeff m p).denom = 1

-- lemma witt_structure_rat_aux (Φ : mv_polynomial bool ℚ) (n : ℕ) :
--   has_integral_coeffs (witt_structure_rat p Φ n) :=
-- begin
--   apply nat.strong_induction_on n, clear n,
--   intros n IH,
-- end

-- #exit

lemma witt_structure_int_prop.aux (Φ : mv_polynomial bool ℤ) (n : ℕ) :
  map (coe : ℤ → ℚ) ((witt_polynomial p n).eval₂ C (witt_structure_int p Φ)) =
  (witt_polynomial p n).eval₂ C (witt_structure_rat p (map coe Φ)) :=
begin
  rw [map_eval₂, map_witt_polynomial],
  congr' 1,
  funext i, apply bar
end

theorem witt_structure_rat_prop (Φ : mv_polynomial bool ℚ) (n) :
  (witt_polynomial p n).eval₂ C (witt_structure_rat p Φ) =
    Φ.eval₂ C (λ b : bool, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  delta witt_structure_rat,
  rw [← function.comp, eval₂_assoc, X_in_terms_of_W_prop₂ p n, eval₂_X]
end

theorem witt_structure_int_prop (Φ : mv_polynomial bool ℤ) :
  ∃! (φ : ℕ → mv_polynomial (bool × ℕ) ℤ), ∀ (n : ℕ),
  (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : bool, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  refine ⟨witt_structure_int p Φ, _, _⟩,
  { intro n,
    apply mv_polynomial.coe_int_rat_map_injective,
    convert witt_structure_rat_prop p (map coe Φ) n,
    { rw [map_eval₂, map_witt_polynomial], congr' 1, funext i, apply bar },
    { rw map_eval₂, congr' 1, funext b, delta function.comp,
      rw [map_rename, map_witt_polynomial], } },
  { intros φ H,
    funext i,
    apply mv_polynomial.coe_int_rat_map_injective,
    rw bar,
    refine congr_fun _ i,
    have := (witt_structure_prop p (map coe Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize H n,
      convert congr_arg (map (coe : ℤ → ℚ)) H using 1,
      { rw [map_eval₂, map_witt_polynomial] },
      { rw map_eval₂, delta function.comp, congr' 1, funext b,
        rw [map_rename, map_witt_polynomial] } },
    { intro n, apply witt_structure_rat_prop } },
end
