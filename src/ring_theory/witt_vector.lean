import data.list.basic
import data.set.finite
import data.nat.prime
import data.nat.choose
import data.mv_polynomial
import algebra.group_power
import group_theory.subgroup
import ring_theory.multiplicity

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
  (s : finset α) (f : α → β) (b : β) (H : ∀ a, b ∣ f a) :
  b ∣ s.sum f :=
by apply finset.induction_on s; intros; simp [*, dvd_add]

end finset

namespace mv_polynomial

open mv_polynomial

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

def coeff (m : ι →₀ ℕ) (p : mv_polynomial ι R) : R := p.to_fun m

@[simp] lemma coeff_add (m : ι →₀ ℕ) (p q : mv_polynomial ι R) :
  coeff m (p + q) = coeff m p + coeff m q := finsupp.add_apply

@[simp] lemma coeff_sub (m : ι →₀ ℕ) (p q : mv_polynomial ι R) :
  coeff m (p - q) = coeff m p - coeff m q := finsupp.sub_apply

@[simp] lemma coeff_zero (m : ι →₀ ℕ) :
  coeff m (0 : mv_polynomial ι R) = 0 := rfl

instance coeff.is_add_group_hom (m : ι →₀ ℕ) :
  is_add_group_hom (coeff m : mv_polynomial ι R → R) :=
⟨coeff_add m⟩

lemma ext (p q : mv_polynomial ι R) :
  (∀ m, coeff m p = coeff m q) → p = q := finsupp.ext
.

@[simp] lemma coeff_zero_X (i : ι) : coeff 0 (X i : mv_polynomial ι R) = 0 := rfl

lemma coeff_sum {X : Type*} (s : finset X) (f : X → mv_polynomial ι R) (m : ι →₀ ℕ) :
  coeff m (s.sum f) = s.sum (λ x, coeff m (f x)) :=
begin
  apply (@finset.sum_hom _ _ _ _ _ _ _ _ _).symm,
  refine @is_add_group_hom.to_is_add_monoid_hom _ _ _ _ _ _,
end

lemma monic_monomial_eq (m) : monomial m (1:R) = (m.prod $ λn e, X n ^ e : mv_polynomial ι R) :=
by simp [monomial_eq]

@[simp] lemma coeff_monomial (m n) (r:R) :
  coeff m (monomial n r : mv_polynomial ι R) = if n = m then r else 0 :=
finsupp.single_apply

@[simp] lemma coeff_C_mul (m) (r : R) (p : mv_polynomial ι R) : coeff m (C r * p) = r * coeff m p :=
begin
  sorry
  -- conv in (r * _) { rw [← @finsupp.sum_single _ _ _ _ _ p, coeff_sum] },
  -- rw [finsupp.mul_def, C, finsupp.sum_single_index],
  -- { simp [coeff_single, finsupp.mul_sum, coeff_sum],
  --   apply sum_congr rfl,
  --   assume i hi, by_cases i = n; simp [h] },
  -- simp
end

lemma coeff_map
  (p : mv_polynomial ι R) (m : ι →₀ ℕ) :
  coeff m (p.map f) = f (coeff m p) :=
begin
  delta map eval₂ finsupp.sum,
  simp only [coeff_sum, coeff_C_mul],
  dsimp,
  sorry
  -- erw [← @finset.sum_hom (ι →₀ ℕ) _ _ (p.support) (coeff m : mv_polynomial ι R → R)],
  -- erw finsupp.sum_apply,
  -- simp [@is_add_group_hom.map_finset_sum (mv_polynomial ι R) _ R _ (coeff m) _ _ _ (p.support) _],
  -- (λ (a : ι →₀ ℕ), C (f (p a)) * finsupp.prod a (λ (n : ι), pow (X n))),
end

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

variables (s : set ℕ+) (α : Type u)

def witt_vectors := s → α

local notation `𝕎` := witt_vectors

def pnat.divisors (n : ℕ+) : set ℕ+ :=
{d | d ∣ n}

noncomputable instance pnat.divisors.fintype (n : ℕ+) : fintype n.divisors :=
finite.fintype $ finite_of_finite_image (subtype.val_injective) $ finite_subset (finite_le_nat n) $
by { rintros _ ⟨_, ⟨c, rfl⟩, rfl⟩, exact nat.le_mul_of_pos_right c.property }

def set.is_truncation_set (s : set ℕ+) : Prop :=
∀ (n : ℕ+), n ∈ s → n.divisors ⊆ s

def fintype.sum {α : Type*} {β : Type*} (f : α → β) [s : fintype α] [add_comm_monoid β] :=
s.elems.sum f

variables [decidable_eq α] [comm_ring α]

noncomputable def witt_polynomial (hs : s.is_truncation_set) (n : s) :
  mv_polynomial s α :=
fintype.sum (λ (d : (n : ℕ+).divisors),
  let d_in_s : (d : ℕ+) ∈ s := hs n n.property d.property in
  C d * (X ⟨d, d_in_s⟩)^((n : ℕ)/d))

local attribute [class] nat.prime
variables (p : ℕ) [nat.prime p]

lemma dvd_sub_pow_of_dvd_sub (a b : α) (h : (p : α) ∣ a - b) (k : ℕ) :
  (p^(k+1) : α) ∣ a^(p^k) - b^(p^k) :=
begin
  rcases h with ⟨c, hc⟩,
  rw sub_eq_iff_eq_add' at hc,
  replace hc := congr_arg (λ x, x^(p^k)) hc,
  simp only [sub_eq_add_neg, add_pow] at hc,
  rw [finset.sum_range_succ, nat.choose_self, nat.cast_one, mul_one,
    nat.sub_self, pow_zero, mul_one] at hc,
  rw [hc, add_sub_cancel'], clear hc,
  apply dvd_sum,
  intros i,
  rw mul_assoc,
  rw mul_pow,
  conv { congr, skip, congr, skip, congr, rw mul_comm },
  apply dvd_mul_of_dvd_right,
  rw mul_assoc,
  apply dvd_mul_of_dvd_right,
  clear a b c,
  by_cases H : (p ^ k) < i,
  { simp [nat.choose_eq_zero_of_lt H] },

end

lemma foo (a b : α) (h : ∃ c, a = b + c * p) (k : ℕ) :
  ∃ d, a^(p^k) = b^(p^k) + d * (p^(k+1)) :=
begin
  rcases h with ⟨c, rfl⟩,
end

lemma prime_ne_zero : p ≠ 0 := nat.pos_iff_ne_zero.mp $ nat.prime.pos ‹_›

open mv_polynomial

variables {R : Type u} [decidable_eq R] [comm_ring R]

theorem range_sum_eq_fin_univ_sum {α} [add_comm_monoid α] (f : ℕ → α) (n) :
  (finset.range n).sum f = finset.univ.sum (λ i : fin n, f i.1) :=
show _ = @multiset.sum α _ ↑(list.map _ _),
by rw [list.map_pmap, list.pmap_eq_map]; refl

def witt_polynomial' (n : ℕ) : mv_polynomial ℕ R :=
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
   Φ.eval₂ C (λ b, ((witt_polynomial p k).eval (λ i, X (b,i))))) (X_in_terms_of_W p n)

theorem witt_structure_prop (Φ : mv_polynomial bool ℚ) :
  ∃! (φ : ℕ → mv_polynomial (bool × ℕ) ℚ), ∀ (n : ℕ),
  (witt_polynomial p n).eval₂ C φ =
    Φ.eval₂ C (λ b : bool, ((witt_polynomial p n).eval (λ i : ℕ, X (b,i)))) :=
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

lemma witt_structure_rat_rec (Φ : mv_polynomial bool ℚ) (n) :
  (witt_structure_rat p Φ n) * C (p^n) =
  Φ.eval₂ C (λ b, ((witt_polynomial p n).eval (λ i, X (b,i)))) -
  (finset.range n).sum (λ i, (C p)^i * (witt_structure_rat p Φ i)^p^(n-i)) :=
begin
  have := @X_in_terms_of_W_aux p _ n,
  replace := congr_arg (eval₂ C (λ k : ℕ,
  Φ.eval₂ C (λ b, ((witt_polynomial p k).eval (λ i, X (b,i)))))) this,
  rw [eval₂_mul, eval₂_C] at this,
  convert this, clear this,
  simp only [eval₂_sub, eval₂_X],
  rw sub_left_inj,
  simp only [eval₂_sum'],
  apply finset.sum_congr rfl,
  intros i hi,
  rw [eval₂_mul, ← C_pow, ← C_pow, eval₂_C, eval₂_pow],
  refl
end

def has_integral_coeffs {ι : Type*} [decidable_eq ι] (p : mv_polynomial ι ℚ) : Prop :=
  ∀ m, (coeff m p).denom = 1

lemma witt_structure_rat_aux (Φ : mv_polynomial bool ℚ) (n : ℕ) :
  has_integral_coeffs (witt_structure_rat p Φ n) :=
begin
  apply nat.strong_induction_on n, clear n,
  intros n IH,
end

def witt_structure_int (Φ : mv_polynomial bool ℤ) (n : ℕ) : mv_polynomial (bool × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (witt_structure_rat p (map int.cast Φ) n)

lemma mv_polynomial.map_injective (I : Type*) [decidable_eq I] :
  function.injective (map int.cast : mv_polynomial I ℤ → mv_polynomial I ℚ) :=
begin
  rw is_add_group_hom.injective_iff _,
  all_goals {try {apply_instance}},
  intros f hf,
  ext c,
  replace hf := congr_arg finsupp.to_fun hf,
  replace hf := congr_fun hf c,
  suffices : (f.to_fun c : ℚ) = (0 : ℤ),
  { rw int.cast_inj at this, convert this, },
  convert hf,
  dsimp [map],
  sorry
end

-- #exit

lemma foo (Φ : mv_polynomial bool ℤ) (n : ℕ) :
  map (int.cast : ℤ → ℚ) (witt_structure_int p Φ n) = witt_structure_rat p (map int.cast Φ) n :=
begin
  apply nat.strong_induction_on n, clear n,
  delta witt_structure_int witt_structure_rat,
  intros n IH,
  rw X_in_terms_of_W_eq,
end

lemma witt_structure_int_prop.aux (Φ : mv_polynomial bool ℤ) (n : ℕ) :
  map int.cast ((witt_polynomial p n).eval₂ C (witt_structure_int p Φ)) =
  (witt_polynomial p n).eval₂ C (witt_structure_rat p (map int.cast Φ)) :=
begin
  induction n,
  -- apply nat.strong_induction_on n, clear n,
  -- intros n IH,
  { delta witt_polynomial,
    simp,
    delta witt_structure_int witt_structure_rat,
    dsimp [X_in_terms_of_W],
    -- simp [X_in_terms_of_W_zero, witt_polynomial_zero],
    -- rw eval₂_X,
},
end

lemma witt_structure_int_prop (Φ : mv_polynomial bool ℤ) :
  ∀ n, (map int.cast (witt_structure_int p Φ n)) = witt_structure_rat p (map int.cast Φ) n :=
begin
  apply congr_fun,
  rw ← witt_structure_prop,
  intro n,
  apply nat.strong_induction_on n, clear n,
  intros n IH,
  delta witt_polynomial,
end
