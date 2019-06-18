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
import data.zmod.quadratic_reciprocity

import tactic.tidy
import tactic.omega
import tactic.explode

universes u v w u₁

local attribute [class] nat.prime
variables (α : Type u) [decidable_eq α] [comm_ring α]
variables (p : ℕ) [nat.prime p]

-- ### FOR_MATHLIB
-- everything in this section should move to other files

lemma nat.map_cast {α : Type*} {β : Type*} (f : α → β) [semiring α] [semiring β] [is_semiring_hom f]
  (n : ℕ) : f (n : α) = n :=
begin
  induction n with n ih, {rw_mod_cast is_add_monoid_hom.map_zero f},
  simp [is_semiring_hom.map_add f, is_semiring_hom.map_one f, ih]
end

section finset

variables {G : Type u} [comm_group G]
variables {H : Type v} [comm_group H]
variables (i : G → H) [is_group_hom i]
variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → G)

-- Generalise this to arbitrary property that is respected by addition/multiplication:
-- example applications: sum_pos, sum_neg, ... others?
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

lemma rat.coe_num_eq_iff (r : ℚ) : (r.num : ℚ) = r ↔ r.denom = 1 :=
begin
  split,
  { intro h,
    rw [rat.coe_int_eq_mk, rat.num_denom r, rat.mk_eq] at h,
    { cases r with n d p c, show d = 1,
      change (rat.mk n d).num * d = n * 1 at h,
      sorry },
    { exact one_ne_zero },
    { apply ne_of_gt, exact_mod_cast r.pos } },
  { intro h,
    rw [← rat.cast_of_int, rat.num_denom r, h, ← rat.mk_nat_eq],
    norm_cast, delta rat.of_int rat.mk_nat, congr,
    simp only [nat.gcd_one_right, int.nat_abs, nat.div_one] },
end

lemma rat.denom_coe_div_eq_one_iff (d n : ℤ) (hd : d ≠ 0) :
  ((n : ℚ) / d).denom = 1 ↔ d ∣ n :=
begin
  split,
  { intro h, refine ⟨(n/d : ℚ).num, _⟩,
    suffices : (n : ℚ) = ↑(d * (n/d : ℚ).num),
    { rwa int.cast_inj at this },
    rw ← rat.coe_num_eq_iff at h,
    rw [int.cast_mul, h, mul_div_cancel'],
    exact_mod_cast hd },
  { rintros ⟨c, rfl⟩, rw [int.cast_mul, mul_div_cancel_left],
    { exact rat.coe_int_denom c },
    { exact_mod_cast hd } }
end

namespace mv_polynomial
variables {σ : Type*} [decidable_eq σ]

lemma int_dvd_iff_dvd_coeff (p : mv_polynomial σ ℤ) (n : ℤ) (h : n ≠ 0) :
  C n ∣ p ↔ ∀ c, n ∣ coeff c p :=
begin
  split,
  { rintros ⟨d, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro H,
    refine ⟨finsupp.map_range (λ k, k/n) (by simp) p, _⟩,
    apply mv_polynomial.ext,
    intro c,
    rw coeff_C_mul,
    dsimp [coeff] at H ⊢,
    rcases H c with ⟨d, H⟩,
    rw [H, int.mul_div_cancel_left _ h] }
end

variables {β : Type*} [decidable_eq β] [comm_semiring β]
variables {γ : Type*} (s : finset γ) (g : γ → mv_polynomial σ α)

@[simp] lemma map_sum (f : α → β) [is_semiring_hom f] :
  map f (s.sum g) = s.sum (λ c, map f (g c)) :=
(finset.sum_hom (map f)).symm

lemma is_integral_iff (p : mv_polynomial σ ℚ) :
  map (coe : ℤ → ℚ) (finsupp.map_range rat.num (rat.coe_int_num 0) p) = p ↔
  ∀ m, (coeff m p).denom = 1 :=
begin
  rw ← ext_iff,
  apply forall_congr,
  intro m,
  rw [coeff_map, ← rat.coe_num_eq_iff],
  exact iff.rfl
end

-- lemma dvd_iff_dvd_coeff (p : mv_polynomial σ α) (a : α) (h : a ≠ 0) :
--   C a ∣ p ↔ ∀ c, a ∣ coeff c p :=
-- begin
--   split,
--   { rintros ⟨d, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
--   { intro h,
--     sorry }
--     -- refine ⟨finsupp.map_range (λ k, k/n) (by simp) φ, _⟩,
--     -- apply mv_polynomial.ext,
--     -- intro c,
--     -- rw [← C_eq_coe_nat, coeff_C_mul],
--     -- dsimp [coeff] at h ⊢,
--     -- rcases h c with ⟨d, h⟩,
--     -- rw [h, int.mul_div_cancel_left, int.nat_cast_eq_coe_nat],
--     -- exact_mod_cast hn }
-- end


end mv_polynomial

namespace modp
variables {α}

notation x ` modᵢ ` I := (ideal.quotient.mk I x)
notation x ` modₛ ` s := (ideal.quotient.mk (ideal.span s) x)
notation x ` modₑ ` a := (ideal.quotient.mk (ideal.span ({a})) x)

@[simp] lemma mod_self (a : α) : (a modₑ a) = 0 :=
begin
  rw ideal.quotient.eq_zero_iff_mem,
  exact ideal.subset_span (set.mem_singleton a)
end

lemma char_one.one_eq_zero [char_p α 1] : (1 : α) = 0 :=
by exact_mod_cast char_p.cast_eq_zero α 1

lemma char_one.elim [char_p α 1] (a b : α) : a = b :=
by rw [← one_mul a, ← one_mul b, char_one.one_eq_zero, zero_mul, zero_mul]

instance char_one_of_is_unit (a : α) (h : is_unit a) :
  char_p (ideal.span ({a} : set α)).quotient 1 :=
⟨begin
  rcases h with ⟨⟨a, b, hab, hba⟩, rfl⟩,
  intro n,
  have helper : ∀ m : ℕ, (m : (ideal.span ({a} : set α)).quotient) =
    ideal.quotient.mk (ideal.span ({a} : set α)) m,
  { intro m, induction m with m ih, {refl}, simp [ih] },
  split,
  { intro hn, exact one_dvd n },
  { rintro ⟨c, rfl⟩,
    rw [helper, nat.cast_mul, nat.cast_one, ← hab, mul_assoc, ideal.quotient.mk_mul, mod_self, zero_mul],
    refl, }
end⟩

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
    cases nat.coprime_or_dvd_of_prime ‹_› n with hn hn,
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
    rw [nat.cast_mul, helper, mod_self, zero_mul] }
end⟩
.

lemma add_pow (a b : α) : ((a + b)^p modₑ (p : α)) = (a^p modₑ (p : α)) + (b^p modₑ (p : α)) :=
begin
  classical,
  by_cases H : is_unit (p : α),
  { haveI := modp.char_one_of_is_unit _ H, exact char_one.elim _ _ },
  { haveI := modp.char_p ‹_› H, simpa using add_pow_char _ ‹_› _ _, apply_instance }
end

end modp

lemma eq_mod_iff_dvd_sub (a b c : α) :
  (a modₑ c) = (b modₑ c) ↔ c ∣ a - b :=
by rw [← sub_eq_zero, ← ideal.quotient.mk_sub,
  ideal.quotient.eq_zero_iff_mem, ideal.mem_span_singleton]

variables {β : Type*} [decidable_eq β] [comm_ring β]
variables {σ : Type*} {τ : Type*} [decidable_eq σ] [decidable_eq τ]
open mv_polynomial

lemma eval₂_mod (p : mv_polynomial σ α) (f : α → β) [is_semiring_hom f] (g₁ : σ → β) (g₂ : σ → β) (b : β)
  (h : ∀ i, (g₁ i modₑ b) = (g₂ i modₑ b)) :
  ((p.eval₂ f g₁) modₑ b) = (p.eval₂ f g₂ modₑ b) :=
begin
  rw [eval₂_comp_right (ideal.quotient.mk _) f g₁, eval₂_comp_right (ideal.quotient.mk _) f g₂,
    function.comp, function.comp],
  all_goals {try {apply_instance}},
  congr, funext i, rw h i,
end

lemma rename_mod (p q : mv_polynomial σ α) (g : σ → τ) (r : mv_polynomial σ α)
  (h : (p modₑ r) = (q modₑ r)) :
  ((p.rename g) modₑ (r.rename g)) = (q.rename g modₑ (r.rename g)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  rcases h with ⟨d, h⟩,
  refine ⟨d.rename g, _⟩,
  rw [← rename_sub, ← rename_mul],
  congr, exact h,
end

lemma rename_mod_C (p q : mv_polynomial σ α) (g : σ → τ) (a : α)
  (h : (p modₑ (C a)) = (q modₑ (C a))) :
  ((p.rename g) modₑ (C a)) = (q.rename g modₑ (C a)) :=
begin
  rwa [← rename_C g, rename_mod], assumption
end

def rat.unit_of_prime : units ℚ :=
⟨p, 1/p,
mul_one_div_cancel (by exact_mod_cast ne_of_gt (nat.prime.pos ‹_›)),
one_div_mul_cancel (by exact_mod_cast ne_of_gt (nat.prime.pos ‹_›))⟩

theorem range_sum_eq_fin_univ_sum {α} [add_comm_monoid α] (f : ℕ → α) (n) :
  (finset.range n).sum f = finset.univ.sum (λ i : fin n, f i.1) :=
show _ = @multiset.sum α _ ↑(list.map _ _),
by rw [list.map_pmap, list.pmap_eq_map]; refl

lemma fermat_little' (a : zmodp p ‹_›) : a^p = a :=
begin
  have ppos : p > 0 := nat.prime.pos ‹_›,
  by_cases h : a = 0,
  { subst a, apply zero_pow ppos },
  { have := zmodp.fermat_little ‹_› h,
    replace := congr_arg (λ x, a * x) this,
    simp at this,
    convert this,
    rw ← pow_succ, congr, clear this h a _inst_3,
    revert ppos p, omega manual nat }
end

lemma int_pol_mod_p (φ : mv_polynomial σ ℤ) :
  ((φ.eval₂ C (λ i, (X i)^p)) modₑ ↑p) = (φ^p modₑ ↑p) :=
begin
  apply mv_polynomial.induction_on φ,
  { intro n, rw [eval₂_C, eq_mod_iff_dvd_sub, ← C_eq_coe_nat, ← C_pow, ← C_sub],
    suffices : (p : ℤ) ∣ n - n^p,
    { rcases this with ⟨d, h⟩, refine ⟨C d, _⟩, rw [h, C_mul, int.nat_cast_eq_coe_nat] },
      rw ← zmodp.eq_zero_iff_dvd_int ‹_›,
      rw [int.cast_sub, int.cast_pow, sub_eq_zero],
      symmetry, apply fermat_little' },
  { intros f g hf hg, rw [eval₂_add, ideal.quotient.mk_add, hf, hg, modp.add_pow] },
  { intros f i hf, rw [eval₂_mul, ideal.quotient.mk_mul, hf, eval₂_X, mul_pow, ideal.quotient.mk_mul] }
end

open mv_polynomial set

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

lemma zrum (a b : α) (h : (a modₑ (p : α)) = (b modₑ (p : α))) (k : ℕ) :
  (a^(p^k) modₑ (p^(k+1) : α)) = (b^(p^k) modₑ (p^(k+1) : α)) :=
begin
  rw eq_mod_iff_dvd_sub at h ⊢,
  apply dvd_sub_pow_of_dvd_sub,
  exact h
end

-- ### end FOR_MATHLIB

-- proper start of this file

variables {R : Type u} [decidable_eq R] [comm_ring R]

def witt_polynomial (n : ℕ) : mv_polynomial ℕ R :=
(finset.range (n+1)).sum (λ i, (C (p^i) * X i ^ (p^(n-i))))

variables (R)

lemma witt_polynomial_zero : (witt_polynomial p 0 : mv_polynomial ℕ R) = X 0 :=
begin
  delta witt_polynomial,
  simp [finset.sum_range_succ, finset.range_zero, finset.sum_empty],
end

variables {R} (pu : units R) (hp : (pu : R) = p)

-- We need p to be invertible for the following definitions
def X_in_terms_of_W (pu : units R) (hp : (pu : R) = p) :
  ℕ → mv_polynomial ℕ R
| n := C ((pu⁻¹ : units R)^n) * (X n - (finset.sum finset.univ (λ i : fin n,
  have _ := i.2, (C (p^(i : ℕ)) * (X_in_terms_of_W i)^(p^(n-i))))))

/- View a polynomial written in terms of basis of Witt polynomials
as a polynomial written in terms of the standard basis.-/
def from_X_to_W_basis : mv_polynomial ℕ R → mv_polynomial ℕ R :=
eval₂ C (X_in_terms_of_W p pu hp)

instance from_X_to_W_basis.is_ring_hom : is_ring_hom (from_X_to_W_basis p pu hp) :=
by delta from_X_to_W_basis; apply_instance

lemma X_in_terms_of_W_eq {n : ℕ} :
  X_in_terms_of_W p pu hp n = C ((pu⁻¹ : units R)^n) *
    (X n - (finset.range n).sum (λ i, C (p^i) * X_in_terms_of_W p pu hp i ^ p ^ (n - i))) :=
by { rw [X_in_terms_of_W, range_sum_eq_fin_univ_sum], refl }

/-
lemma X_in_terms_of_W_zero : X_in_terms_of_W p pu hp 0 = witt_polynomial p 0 :=
begin
  rw X_in_terms_of_W_eq,
  rw finset.range_zero,
  rw finset.sum_empty,
  rw witt_polynomial_zero,
  simp
end
-/

lemma X_in_terms_of_W_aux (n) : C (p^n : R) * X_in_terms_of_W p pu hp n =
  X n - (finset.range n).sum (λ i, C (p^i) * (X_in_terms_of_W p pu hp i)^p^(n-i)) :=
by rw [X_in_terms_of_W_eq, ← mul_assoc, ← C_mul, ← mul_pow, ← hp, pu.mul_inv, one_pow, C_1, one_mul]

lemma X_in_terms_of_W_prop_aux
  (f : mv_polynomial ℕ R → mv_polynomial ℕ R) [is_ring_hom f]
  (fC : ∀ (a : R), f (C a) = C a)
  (fX : ∀ (n : ℕ), f (X n) = @witt_polynomial p _ R _ _ n)
  (n : ℕ) : f (X_in_terms_of_W p pu hp n) = X n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [is_ring_hom.map_mul f, is_ring_hom.map_sub f, fC, fX, (finset.sum_hom f).symm],
  rw [finset.sum_congr rfl, (_ : @witt_polynomial p _ R _ _ n -
    (finset.range n).sum (λ i, C (p^i) * (X i)^p^(n-i)) = C (p^n) * X n)],
  { rw [← mul_assoc, ← C_mul, ← mul_pow, ← hp, pu.inv_mul, one_pow, C_1, one_mul] },
  { simp [witt_polynomial, nat.sub_self],
    rw finset.sum_range_succ,
    simp },
  { intros i h,
    rw finset.mem_range at h,
    simp only [is_ring_hom.map_mul f, is_semiring_hom.map_pow f, fC, function.comp_app],
    rw H _ h }
end

lemma X_in_terms_of_W_prop (n : ℕ) : (X_in_terms_of_W p pu hp n).eval₂ C (witt_polynomial p) = X n :=
begin
  apply X_in_terms_of_W_prop_aux,
  { apply eval₂_C },
  { apply eval₂_X }
end

lemma X_in_terms_of_W_prop₂ (k : ℕ) : (witt_polynomial p k).eval₂ C (X_in_terms_of_W p pu hp) = X k :=
begin
  suffices : from_X_to_W_basis p pu hp (C (p^k) * X k) +
    from_X_to_W_basis p pu hp (finset.sum (finset.range k) (λ (i : ℕ), C (p^i) * (X i)^p^(k-i))) = X k,
  { simpa [witt_polynomial, finset.sum_range_succ, from_X_to_W_basis] },
  suffices : ∀ i, from_X_to_W_basis p pu hp (C (p^i) * (X i)^p^(k-i)) =
    C (p^i) * (X_in_terms_of_W p pu hp i)^p^(k-i),
  { rw [from_X_to_W_basis, eval₂_mul, eval₂_C, eval₂_X, X_in_terms_of_W_eq,
        ← mul_assoc, ← C_mul, ← mul_pow, ← hp, pu.mul_inv, one_pow, C_1, one_mul,
        ← finset.sum_hom (eval₂ C $ X_in_terms_of_W p pu hp),
        sub_add_eq_add_sub, sub_eq_iff_eq_add, hp],
    congr,
    funext i,
    exact this i },
  intro i,
  rw [from_X_to_W_basis, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
end

variables {idx : Type*} [decidable_eq idx]

def witt_structure_rat (Φ : mv_polynomial idx ℚ) : ℕ → mv_polynomial (idx × ℕ) ℚ :=
λ n, eval₂ C (λ k : ℕ,
   Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (prod.mk b))))
     (X_in_terms_of_W p (rat.unit_of_prime p) rfl n)

theorem witt_structure_rat_prop (Φ : mv_polynomial idx ℚ) (n) :
  (witt_polynomial p n).eval₂ C (witt_structure_rat p Φ) =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (prod.mk b))) :=
begin
  delta witt_structure_rat,
  rw [eval₂_assoc (C : ℚ → mv_polynomial (idx × ℕ) ℚ), X_in_terms_of_W_prop₂ p _ _ n, eval₂_X]
end

theorem witt_structure_prop_exists_unique (Φ : mv_polynomial idx ℚ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℚ), ∀ (n : ℕ),
  (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (prod.mk b))) :=
begin
  refine ⟨witt_structure_rat p Φ, _, _⟩,
  { intro n, apply witt_structure_rat_prop },
  { intros φ H,
    unfold witt_structure_rat,
    funext n,
    rw show φ n = ((X_in_terms_of_W p (rat.unit_of_prime p) rfl n).eval₂ C (witt_polynomial p)).eval₂ C φ,
    { rw [X_in_terms_of_W_prop p, eval₂_X] },
    rw ← eval₂_assoc,
    congr,
    funext k,
    exact H k },
end

lemma witt_structure_rat_rec_aux (Φ : mv_polynomial idx ℚ) (n) :
  C (p^n : ℚ) * (witt_structure_rat p Φ n) =
  Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (prod.mk b))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  have := @X_in_terms_of_W_aux p _ _ _ _ (rat.unit_of_prime p) rfl n,
  replace := congr_arg (eval₂ C (λ k : ℕ,
    Φ.eval₂ C (λ b, ((witt_polynomial p k).rename (prod.mk b))))) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  conv_rhs { simp only [eval₂_sub, eval₂_X] },
  rw sub_left_inj,
  simp only [eval₂_sum],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, eval₂_C, eval₂_pow],
  refl
end

lemma witt_structure_rat_rec (Φ : mv_polynomial idx ℚ) (n) :
  (witt_structure_rat p Φ n) = C (1/p^n) *
  (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (prod.mk b))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p Φ i)^p^(n-i))) :=
begin
  rw [← witt_structure_rat_rec_aux p Φ n, ← mul_assoc,
      ← C_mul, one_div_mul_cancel, C_1, one_mul],
  exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›))
end

def witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) : mv_polynomial (idx × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n)
.

section
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
    repeat {rw [coeff_C_mul m, coeff_X]},
    rw is_ring_hom.map_mul f,
    split_ifs;
    [ rw is_ring_hom.map_one f, rw is_ring_hom.map_zero f ];
    simp only [mul_one, mul_zero],
    rw is_semiring_hom.map_pow f, congr,
    exact nat.map_cast f p },
  all_goals {apply_instance}
end

end

lemma coeff_witt_polynomial {i n : ℕ} (c : ℕ →₀ ℕ) (hi : i ∈ c.support)
  (hc : coeff c (witt_polynomial p n : mv_polynomial ℕ R) ≠ 0) : i < n + 1 :=
begin
  rw [witt_polynomial, ← finset.sum_hom (coeff c)] at hc,
  work_on_goal 0 {
    rcases finset.exists_ne_zero_of_sum_ne_zero hc with ⟨j, hj, hcj⟩,
    simp only [X_pow_eq_single, C_mul_monomial, coeff_monomial] at hcj,
    split_ifs at hcj,
    { subst c, rw finsupp.mem_support_single at hi,
      cases hi, subst i, rwa finset.mem_range at hj },
    { contradiction } },
  exact coeff.is_add_monoid_hom c
end

def doh {α : Type*} [comm_ring α] : add_comm_monoid α := by apply_instance
def dah {α : Type*} [comm_ring α] : add_monoid α := by apply_instance

def bah {α : Type*} [comm_ring α] (n : ℕ) :
  is_add_monoid_hom (ideal.quotient.mk (ideal.span ({((p^(n+1) : ℕ) : α)} : set α))) :=
by apply_instance
.

def boh {α : Type*} {β : Type*} [comm_semiring α] [comm_semiring β] (f : α → β) [is_semiring_hom f] :
  is_add_monoid_hom f := by apply_instance

lemma witt_polynomial_mod_pow_p (n : ℕ) :
  ((witt_polynomial p (n+1) : mv_polynomial ℕ ℤ) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) =
  (((witt_polynomial p n).eval₂ C (λ i, ((X i)^p))) modₑ (↑(p^(n+1)) : mv_polynomial ℕ ℤ)) :=
begin
  delta witt_polynomial,
  rw [finset.sum_range_succ, ideal.quotient.mk_add, ideal.quotient.mk_mul],
  rw [← nat.cast_pow, ← C_eq_coe_nat, modp.mod_self],
  rw [← finset.sum_hom (ideal.quotient.mk _),
      eval₂_sum,
      ← finset.sum_hom (ideal.quotient.mk _)],
  all_goals {try { apply doh }},
  convert zero_add _ using 1,
  congr' 1,
  work_on_goal 2 {
    apply finset.sum_congr rfl,
    intros i hi,
    rw finset.mem_range at hi, replace hi := nat.le_of_lt_succ hi,
    rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← pow_mul],
    congr,
    rw [mul_comm, ← nat.pow_succ],
    congr,
    exact nat.succ_sub hi },
  all_goals { try {apply dah} },
  -- { refine @boh _ _ _ _ _ _, },
end
.

namespace witt_structure_int_prop_aux

variables {ι : Type*} [decidable_eq ι]
variables {S : Type*} [decidable_eq S] [comm_ring S]
variables {T : Type*} [decidable_eq T] [comm_ring T]

lemma induction_step (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < n → map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  map (coe : ℤ → ℚ) (Φ.eval₂ C (λ b, ((witt_polynomial p n).rename (prod.mk b))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_int p Φ i)^p^(n-i))) =
  ((map coe Φ).eval₂ C (λ b, ((witt_polynomial p n).rename (prod.mk b))) -
  (finset.range n).sum (λ i, C (p^i) * (witt_structure_rat p (map coe Φ) i)^p^(n-i))) :=
begin
  simp only [map_sub, map_eval₂, function.comp, map_rename, map_witt_polynomial, map_sum],
  congr' 1,
  apply finset.sum_congr rfl,
  intros i hi,
  rw finset.mem_range at hi,
  specialize IH i hi,
  rw [map_mul, map_C, map_pow, IH],
  norm_cast
end
.

lemma baz (φ : mv_polynomial ι ℤ) (c) (n : ℤ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (coe : ℤ → ℚ) φ)).denom = 1 ↔ n ∣ coeff c φ :=
begin
  rw [coeff_C_mul, coeff_map, mul_comm, ← div_eq_mul_one_div],
  apply rat.denom_coe_div_eq_one_iff _ _ hn
end

/-
lemma baz_nat (φ : mv_polynomial ι ℤ) (c) (n : ℕ) (hn : n ≠ 0) :
  (coeff c (C (1 / (n : ℚ)) * map (coe : ℤ → ℚ) φ)).denom = 1 ↔ (n : ℤ) ∣ coeff c φ :=
begin
  have := baz φ c n (by exact_mod_cast hn),
  rwa [show ((n : ℤ) : ℚ) = n, by simp] at this,
end
-/
.

lemma blur (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m : ℕ, m < (n + 1) → map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  Φ.eval₂ C (λ (i : idx), rename (prod.mk i) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n))) =
  (witt_polynomial p n).eval₂ C (λ (i : ℕ), (witt_structure_int p Φ i).eval₂ C $ λ i, (X i)^p) :=
calc Φ.eval₂ C (λ (i : idx), rename (prod.mk i) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n))) =
  (Φ.eval₂ C (λ (b : idx), rename (prod.mk b) (witt_polynomial p n))).eval₂ C (λ k, X k ^ p) :
    begin
      rw ← eval₂_assoc,
      simp only [rename_prodmk_eval₂, eval₂_rename, rename_pow, rename_X]
    end
  ... = _ :
  begin
  apply mv_polynomial.map_injective (coe : ℤ → ℚ) (λ m n h, by exact_mod_cast h),
  simp only [map_eval₂, function.comp, map_rename, rename_prodmk_eval₂, map_witt_polynomial],
  rw [← witt_structure_rat_prop, eval₂_assoc],
  dsimp,
  suffices : eval₂ C (witt_structure_rat p (map coe Φ)) (witt_polynomial p n) =
    eval₂ C (λ (t : ℕ), map coe (witt_structure_int p Φ t)) (witt_polynomial p n),
  { sorry },
  apply eval₂_congr,
  intros i c hi hc,
  rw IH,
  exact coeff_witt_polynomial p c hi hc,
  end
.

lemma rec_step (Φ : mv_polynomial idx ℤ) (n : ℕ)
  (IH : ∀ m < (n+1), map coe (witt_structure_int p Φ m) = witt_structure_rat p (map coe Φ) m) :
  (eval₂ C (λ i, rename (prod.mk i) (witt_polynomial p (n+1))) Φ modₑ ↑(p^(n+1))) =
    (finset.sum (finset.range (nat.succ n))
         (λ (i : ℕ), C (p^i) * witt_structure_int p Φ i ^ p ^ (n+1 - i)) modₑ ↑(p^(n+1))) :=
calc _ = (Φ.eval₂ C (λ i, rename (prod.mk i) (witt_polynomial p (n+1))) modₑ ↑(p^(n+1))) : rfl
  ...  = (Φ.eval₂ C (λ i, rename (prod.mk i) (eval₂ C (λ i, ((X i)^p)) (witt_polynomial p n))) modₑ ↑(p^(n+1))) :
  begin
    apply eval₂_mod, intro i,
    rw ← C_eq_coe_nat,
    apply rename_mod_C,
    rw C_eq_coe_nat,
    exact witt_polynomial_mod_pow_p p n,
  end
  ... = _ :
  begin
    rw blur p Φ n IH,
    delta witt_polynomial,
    conv_lhs { congr, simp [eval₂_sum] },
    rw [← finset.sum_hom (ideal.quotient.mk _), ← finset.sum_hom (ideal.quotient.mk _)],
    { apply finset.sum_congr rfl,
      intros i hi,
      rw finset.mem_range at hi, replace hi := nat.le_of_lt_succ hi,
      rw [← C_pow],
      rw [show (p:ℤ)^i = (p^i : ℕ), by simp, ← int.nat_cast_eq_coe_nat, C_eq_coe_nat],
      rw [eq_mod_iff_dvd_sub, ← mul_sub],
      rw show p^(n+1) = p^i * p^(n+1-i),
      { rw ← nat.pow_add, congr' 1, clear IH, revert hi i n, omega manual nat },
      rw nat.cast_mul,
      apply mul_dvd_mul_left,
      rw show n + 1 - i = n - i + 1,
      { exact nat.succ_sub hi },
      rw nat.cast_pow,
      rw [nat.pow_succ, mul_comm, pow_mul],
      apply dvd_sub_pow_of_dvd_sub,
      rw ← eq_mod_iff_dvd_sub,
      apply int_pol_mod_p },
      apply doh, all_goals {apply bah}
  end

lemma map_witt_structure_int (Φ : mv_polynomial idx ℤ) (n : ℕ) :
  map (coe : ℤ → ℚ) (witt_structure_int p Φ n) = witt_structure_rat p (map (coe : ℤ → ℚ) Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  erw mv_polynomial.is_integral_iff,
  intro c,
  rw witt_structure_rat_rec p _ n,
  rw ← induction_step p Φ n IH,
  rw show (p : ℚ)^n = ((p^n : ℕ) : ℤ), by simp,
  rw baz,
  work_on_goal 1 { rw int.coe_nat_pow, apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  induction n with n ih, {simp}, clear ih, revert c,
  rw ← int_dvd_iff_dvd_coeff,
  work_on_goal 1 { suffices : (p ^ n.succ : ℤ) ≠ 0, { exact_mod_cast this },
    apply pow_ne_zero, exact_mod_cast ne_of_gt (nat.prime.pos ‹_›) },
  rw show (C ↑(p ^ n.succ) : mv_polynomial (idx × ℕ) ℤ) = ↑(p^(n+1)),
  { rw [← C_eq_coe_nat, int.nat_cast_eq_coe_nat] },
  rw ← eq_mod_iff_dvd_sub,
  apply rec_step p Φ n IH
end
.

end witt_structure_int_prop_aux

section
open witt_structure_int_prop_aux

theorem witt_structure_int_prop (Φ : mv_polynomial idx ℤ) (n) :
  (witt_polynomial p n).eval₂ C (witt_structure_int p Φ) =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  apply mv_polynomial.map_injective (coe : ℤ → ℚ) (λ m n h, by exact_mod_cast h),
  convert witt_structure_rat_prop p (map coe Φ) n,
  { rw [map_eval₂, map_witt_polynomial], congr' 1, funext i, apply map_witt_structure_int },
  { rw map_eval₂, congr' 1, funext b, delta function.comp,
    rw [map_rename, map_witt_polynomial], }
end

theorem witt_structure_int_exists_unique (Φ : mv_polynomial idx ℤ) :
  ∃! (φ : ℕ → mv_polynomial (idx × ℕ) ℤ),
  ∀ (n : ℕ), (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : idx, ((witt_polynomial p n).rename (λ i : ℕ, (b,i)))) :=
begin
  refine ⟨witt_structure_int p Φ, _, _⟩,
  { apply witt_structure_int_prop },
  { intros φ H,
    funext i,
    apply mv_polynomial.map_injective (coe : ℤ → ℚ) (λ m n h, by exact_mod_cast h),
    rw map_witt_structure_int,
    refine congr_fun _ i,
    have := (witt_structure_prop_exists_unique p (map coe Φ)),
    apply unique_of_exists_unique this,
    { clear this, intro n,
      specialize H n,
      convert congr_arg (map (coe : ℤ → ℚ)) H using 1,
      { rw [map_eval₂, map_witt_polynomial] },
      { rw map_eval₂, delta function.comp, congr' 1, funext b,
        rw [map_rename, map_witt_polynomial] } },
    { intro n, apply witt_structure_rat_prop } },
end
.

end

theorem witt_structure_prop (Φ : mv_polynomial idx ℤ) (n) :
  (witt_polynomial p n).eval₂ C (λ i, map (coe : ℤ → R) (witt_structure_int p Φ i)) =
  (map coe Φ).eval₂ C (λ b, ((witt_polynomial p n).rename (λ i, (b,i)))) :=
begin
  have := witt_structure_int_prop p Φ n,
  replace := congr_arg (λ ψ, map (coe : ℤ → R) ψ) this,
  dsimp at this ⊢,
  rw [map_eval₂, map_eval₂, map_witt_polynomial] at this,
  simp only [function.comp, map_rename] at this ⊢,
  erw this, clear this,
  dsimp,
  suffices : (λ (x : idx), rename (prod.mk x) (map (coe : ℤ → R) (witt_polynomial p n))) =
    (λ (b : idx), rename (prod.mk b) (witt_polynomial p n)),
  { replace := congr_arg (λ g, eval₂ C g (map coe Φ)) this,
    dsimp at this, exact this },
  funext i, rw map_witt_polynomial
end

def witt_add : ℕ → mv_polynomial (bool × ℕ) ℤ := witt_structure_int p (X tt + X ff)

def witt_mul : ℕ → mv_polynomial (bool × ℕ) ℤ := witt_structure_int p (X tt * X ff)

def witt_neg : ℕ → mv_polynomial (unit × ℕ) ℤ := witt_structure_int p (-X unit.star)

@[simp] lemma witt_add_zero : witt_add p 0 = X (tt, 0) + X (ff, 0) :=
dec_trivial

@[simp] lemma witt_mul_zero : witt_mul p 0 = X (tt, 0) * X (ff, 0) :=
dec_trivial

include p
def witt_vectors (α : Type*) := ℕ → α
omit p

local notation `𝕎` := witt_vectors -- type as `𝕎`

namespace witt_vectors
section map
open function
variables {α' : Type*} {β' : Type*} {S : Type*} [comm_ring S]

instance : functor (𝕎 p) :=
{ map := λ α β f v, f ∘ v,
  map_const := λ α β a v, λ _, a }

instance : is_lawful_functor (𝕎 p) :=
{ map_const_eq := λ α β, rfl,
  id_map := λ α v, rfl,
  comp_map := λ α β γ f g v, rfl }

section ring_data

variables (α') [comm_ring α']

instance : has_zero (𝕎 p α') :=
⟨λ _, 0⟩

variable {α'}

def Teichmuller (a : α') : 𝕎 p α'
| 0 := a
| (n+1) := 0

@[simp] lemma Teichmuller_zero : Teichmuller p (0:α') = 0 :=
funext $ λ n, match n with | 0 := rfl | (n+1) := rfl end

variable (α')

instance : has_one (𝕎 p α') :=
⟨Teichmuller p 1⟩

instance : has_add (𝕎 p α') :=
⟨λ x y n, (witt_add p n).eval₂ (coe : ℤ → α') $ λ bn, cond bn.1 (x bn.2) (y bn.2)⟩

lemma add_def (x y : 𝕎 p α') :
  x + y = λ n, (witt_add p n).eval₂ (coe : ℤ → α') $ λ bn, cond bn.1 (x bn.2) (y bn.2) := rfl

instance : has_mul (𝕎 p α') :=
⟨λ x y n, (witt_mul p n).eval₂ (coe : ℤ → α') $ λ bn, cond bn.1 (x bn.2) (y bn.2)⟩

lemma mul_def (x y : 𝕎 p α') :
  x * y = λ n, (witt_mul p n).eval₂ (coe : ℤ → α') $ λ bn, cond bn.1 (x bn.2) (y bn.2) := rfl

instance : has_neg (𝕎 p α') :=
⟨λ x n, (witt_neg p n).eval₂ (coe : ℤ → α') $ λ n, x n.2⟩

lemma neg_def (x : 𝕎 p α') :
  -x = λ n, (witt_neg p n).eval₂ (coe : ℤ → α') $ λ n, x n.2 := rfl

variable {R}

@[simp] lemma Teichmuller_one : Teichmuller p (1:R) = 1 := rfl

end ring_data

variable {p}

def ghost_component (n : ℕ) (w : 𝕎 p R) : R :=
(witt_polynomial p n).eval w

def map (f : α' → β') : 𝕎 p α' → 𝕎 p β' := λ w, f ∘ w

lemma map_injective (f : α' → β') (hf : injective f) :
  injective (map f : 𝕎 p α' → 𝕎 p β') :=
λ x y h, funext $ λ n, hf $ by exact congr_fun h n

lemma map_surjective (f : α' → β') (hf : surjective f) :
  surjective (map f : 𝕎 p α' → 𝕎 p β') :=
λ x, ⟨λ n, classical.some $ hf $ x n,
by { funext n, dsimp [map], rw classical.some_spec (hf (x n)) }⟩

variables (f : R → S) [is_ring_hom f]

@[simp] lemma map_zero : map f (0 : 𝕎 p R) = 0 :=
funext $ λ n, is_ring_hom.map_zero f

@[simp] lemma map_one : map f (1 : 𝕎 p R) = 1 :=
funext $ λ n,
match n with
| 0     := is_ring_hom.map_one f
| (n+1) := is_ring_hom.map_zero f
end

@[simp] lemma map_add (x y : 𝕎 p R) :
  map f (x + y) = map f x + map f y :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_mul (x y : 𝕎 p R) :
  map f (x * y) = map f x * map f y :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  { funext bn, cases bn with b i,
    exact match b with | tt := rfl | ff := rfl end },
  recover, all_goals {apply_instance},
end

@[simp] lemma map_neg (x : 𝕎 p R) :
  map f (-x) = -map f x :=
funext $ λ n,
begin
  show f (eval₂ coe _ _) = eval₂ coe _ _,
  rw eval₂_comp_left f,
  congr' 1,
  { exact int.eq_cast' (f ∘ coe) },
  recover, all_goals {apply_instance},
end

end map

variable {p}

def ghost_map : 𝕎 p R → (ℕ → R) := λ w n, ghost_component n w

@[simp] lemma ghost_map.zero : ghost_map (0 : 𝕎 p R) = 0 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  apply finset.sum_eq_zero,
  intros i hi,
  rw [eval₂_mul, eval₂_pow, eval₂_X],
  convert mul_zero _,
  apply zero_pow _,
  apply nat.pow_pos,
  apply nat.prime.pos, assumption,
end

@[simp] lemma ghost_map.one : ghost_map (1 : 𝕎 p R) = 1 :=
funext $ λ n,
begin
  delta ghost_map ghost_component witt_polynomial eval,
  rw eval₂_sum,
  have : 0 ∈ finset.range (n+1),
  { rw finset.mem_range, exact nat.succ_pos n },
  rw ← finset.insert_erase this,
  rw finset.sum_insert (finset.not_mem_erase 0 (finset.range (n + 1))),
  convert add_zero _,
  { apply finset.sum_eq_zero, intros i hi,
    rw [eval₂_mul, eval₂_pow, eval₂_X],
    rw finset.mem_erase at hi,
    suffices H : (1 : 𝕎 p R) i = 0,
    { rw [H, zero_pow, mul_zero], apply nat.pow_pos, exact nat.prime.pos ‹_› },
    rw ← Teichmuller_one, cases hi with hi bla, revert hi,
    exact match i with
    | 0 := λ H, false.elim (H rfl)
    | (n+1) := λ H, rfl
    end },
  { rw [eval₂_mul, eval₂_pow, eval₂_X, eval₂_C],
    dsimp, rw one_mul, symmetry,
    apply one_pow }
end

variable {R}

@[simp] lemma ghost_map.add (x y : 𝕎 p R) :
  ghost_map (x + y) = ghost_map x + ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt + X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_add witt_add, dsimp [eval],
    rw ← eval₂_assoc _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_add, eval₂_add, eval_add],
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (coe : ℤ → R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.mul (x y : 𝕎 p R) :
  ghost_map (x * y) = ghost_map x * ghost_map y :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (bool × ℕ) R), ψ.eval $ λ (bn : bool × ℕ), cond bn.1 (x bn.2) (y bn.2)) (witt_structure_prop p (X tt * X ff) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_mul witt_mul, dsimp [eval],
    rw ← eval₂_assoc _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_mul, eval₂_mul, eval_mul],
    congr' 1,
    all_goals {
      erw [mv_polynomial.map_X (coe : ℤ → R), eval₂_X, eval_rename_prodmk],
      congr } }
end

@[simp] lemma ghost_map.neg (x : 𝕎 p R) :
  ghost_map (-x) = - ghost_map x :=
funext $ λ n,
begin
  delta ghost_map ghost_component,
  have := congr_arg (λ (ψ : mv_polynomial (unit × ℕ) R), ψ.eval $ λ (bn : unit × ℕ), (x bn.2)) (witt_structure_prop p (-X unit.star) n),
  convert this using 1; clear this,
  { delta witt_vectors.has_neg witt_neg, dsimp [eval],
    rw ← eval₂_assoc _ _ _ _,
    work_on_goal 0 { congr' 1, funext i, apply eval₂_eq_eval_map },
    all_goals {try {assumption}, try {apply_instance}} },
  { dsimp,
    rw [mv_polynomial.map_neg, map_X],
    have := eval_rename_prodmk (witt_polynomial p n) (λ i : unit × ℕ, x i.2) (),
    dsimp at this,
    rw ← this, clear this,
    rw ← eval_neg,
    congr' 1,
    have := eval₂_neg (X ()) C (λ (b : unit), rename (prod.mk b) (witt_polynomial p n : mv_polynomial ℕ R)),
    rw eval₂_X at this,
    dsimp at this ⊢,
    exact this.symm }
end
.

lemma ghost_map.equiv_of_unit (pu : units R) (hp : (pu : R) = p) :
  𝕎 p R ≃ (ℕ → R) :=
{ to_fun := ghost_map,
  inv_fun := λ x n, (X_in_terms_of_W p pu hp n).eval x,
  left_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc (id : R → R),
    { convert eval_X _, exact X_in_terms_of_W_prop p pu hp n },
    all_goals { assumption <|> apply_instance }
  end,
  right_inv :=
  begin
    intro x, funext n,
    dsimp [ghost_map, ghost_component, eval],
    rw eval₂_assoc (id : R → R),
    { convert eval_X _,
      { simp only [eval₂_X, X_in_terms_of_W_prop₂] },
      { apply_instance } },
    all_goals { assumption <|> apply_instance }
  end }

lemma ghost_map.bijective_of_unit (pu : units R) (hp : (pu : R) = p) :
  function.bijective (ghost_map : 𝕎 p R → ℕ → R) :=
let H := (ghost_map.equiv_of_unit pu hp).bijective in
by { convert H using 1, delta ghost_map.equiv_of_unit, refl }

section
open function
variables {α' : Type*} [has_zero α'] [has_one α'] [has_add α'] [has_mul α'] [has_neg α']
variables {β' : Type*} [comm_ring β']

def comm_ring_of_injective (f : α' → β') (inj : injective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ {x y}, f (x + y) = f x + f y)
  (mul : ∀ {x y}, f (x * y) = f x * f y) (neg : ∀ {x}, f (-x) = - f x) :
  comm_ring α' :=
begin
  refine_struct { ..‹has_zero α'›, ..‹has_one α'›, ..‹has_add α'›, ..‹has_mul α'›, ..‹has_neg α'› },
  all_goals { intros, apply inj,
    repeat { erw zero <|> erw one <|> erw add <|> erw mul <|> erw neg },
    try {simp [mul_assoc, mul_add, add_mul] } },
  rw mul_comm
end

def comm_ring_of_surjective (f : β' → α') (sur : surjective f)
  (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ {x y}, f (x + y) = f x + f y)
  (mul : ∀ {x y}, f (x * y) = f x * f y) (neg : ∀ {x}, f (-x) = - f x) :
  comm_ring α' :=
begin
  refine_struct { ..‹has_zero α'›, ..‹has_one α'›, ..‹has_add α'›, ..‹has_mul α'›, ..‹has_neg α'› },
  all_goals {
    try { intro a, rcases sur a with ⟨a, rfl⟩ },
    try { intro b, rcases sur b with ⟨b, rfl⟩ },
    try { intro c, rcases sur c with ⟨c, rfl⟩ },
    repeat { erw ← zero <|> erw ← one <|> erw ← add <|> erw ← mul <|> erw ← neg },
    try {simp [mul_assoc, mul_add, add_mul] } },
  rw mul_comm
end

variable (R)

def mv_polynomial.counit : mv_polynomial R ℤ → R :=
eval₂ coe id

instance mv_polynomial.counit.is_ring_hom : is_ring_hom (mv_polynomial.counit R) :=
by delta mv_polynomial.counit; apply_instance

lemma counit_surjective : surjective (mv_polynomial.counit R) :=
λ r, ⟨X r, eval₂_X _ _ _⟩

end

variable (R)

def aux₁ : comm_ring (𝕎 p (mv_polynomial R ℚ)) :=
comm_ring_of_injective (ghost_map)
  (ghost_map.bijective_of_unit ((rat.unit_of_prime p).map C)
  (by rw ← C_eq_coe_nat; refl)).1
  (@ghost_map.zero p _ (mv_polynomial R ℚ) _ _)
  (ghost_map.one) (ghost_map.add) (ghost_map.mul) (ghost_map.neg)

local attribute [instance] aux₁
.

def aux₂ : comm_ring (𝕎 p (mv_polynomial R ℤ)) :=
have hom : is_ring_hom (mv_polynomial.map coe : mv_polynomial R ℤ → mv_polynomial R ℚ), by apply_instance,
comm_ring_of_injective (map $ mv_polynomial.map (coe : ℤ → ℚ))
  (map_injective _ $ mv_polynomial.map_injective (coe : ℤ → ℚ) (λ m n h, by exact_mod_cast h))
  (@map_zero _ _ _ _ _ _ _ _ hom)
  (@map_one _ _ _ _ _ _ _ _ hom)
  (@map_add _ _ _ _ _ _ _ _ hom)
  (@map_mul _ _ _ _ _ _ _ _ hom)
  (@map_neg _ _ _ _ _ _ _ _ hom)

local attribute [instance] aux₂
.

instance : comm_ring (𝕎 p R) :=
comm_ring_of_surjective
(map $ mv_polynomial.counit _) (map_surjective _ $ counit_surjective _)
  (@map_zero _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_one _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_add _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_mul _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))
  (@map_neg _ _ _ _ _ _ _ _ (mv_polynomial.counit.is_ring_hom R))

namespace map
variables {S : Type*} [decidable_eq S] [comm_ring S]

instance (f : R → S) [is_ring_hom f] : is_ring_hom (map f : 𝕎 p R → 𝕎 p S) :=
{ map_one := map_one f,
  map_mul := map_mul f,
  map_add := map_add f }

end map

namespace ghost_map

instance : is_ring_hom (ghost_map : 𝕎 p R → ℕ → R) :=
{ map_one := one,
  map_mul := mul,
  map_add := add }

end ghost_map

variable {R}

def Verschiebung : 𝕎 p R → 𝕎 p R :=
λ x n, match n with
| 0     := 0
| (n+1) := x n
end

@[simp] lemma Verschiebung_zero : Verschiebung (0 : 𝕎 p R) = 0 :=
funext $ λ n, match n with | 0 := rfl | (n+1) := rfl end

-- TODO(jmc): prove these
-- lemma Teichmuller_mul (x y : R) :
--   Teichmuller p (x * y) = Teichmuller p x * Teichmuller p y :=
-- sorry

-- lemma Verschiebung_add (x y : R) :
--   Verschiebung (x + y) = Verschiebung x + Verschiebung y :=
-- sorry

end witt_vectors
