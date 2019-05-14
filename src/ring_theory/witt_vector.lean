import data.nat.prime
import algebra.group_power
import data.mv_polynomial
import group_theory.subgroup

universes u v w u₁

-- ### FOR_MATHLIB
-- everything in this section should move to other files

section ring_hom_commutes_with_stuff

variables {R : Type u} [comm_ring R]
variables {S : Type v} [comm_ring S]
variables (i : R → S) [is_ring_hom i]

section finset

open finset

variables {X : Type w} [decidable_eq X] (s : finset X) (f : X → R)

lemma ring_hom_sum.finset : i (sum s f) = sum s (i ∘ f) :=
begin
  apply finset.induction_on s,
  { repeat { rw sum_empty },
    exact is_ring_hom.map_zero i },
  { intros x s' hx ih,
    repeat { rw sum_insert hx },
    rw [is_ring_hom.map_add i, ←ih] }
end

end finset

end ring_hom_commutes_with_stuff

-- ### end FOR_MATHLIB

-- proper start of this file

local attribute [class] nat.prime

variables (p : ℕ) [nat.prime p]

lemma prime_ne_zero : p ≠ 0 := nat.pos_iff_ne_zero.mp $ nat.prime.pos ‹_›

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

lemma X_in_terms_of_W_aux {n} :
  X n - (X_in_terms_of_W p n * C(p^n)) =
  (finset.range n).sum (λ i, C p ^ i * X_in_terms_of_W p i ^ p ^ (n - i)) :=
begin
  rw sub_eq_iff_eq_add,
  rw add_comm,
  rw ← sub_eq_iff_eq_add,
  rw X_in_terms_of_W_eq,
  rw mul_assoc,
  rw ← C_mul,
  convert (mul_one _).symm,
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
  (fC : ∀ (a : ℚ), f (C a) = C a)
  (fX : ∀ (n : ℕ), f (X n) = @witt_polynomial p _ ℚ _ _ n)
  (n : ℕ) : f (X_in_terms_of_W p n) = X n :=
begin
  apply nat.strong_induction_on n,
  clear n, intros n H,
  rw [X_in_terms_of_W_eq],
  simp only [is_ring_hom.map_mul f, is_ring_hom.map_sub f, fC, fX, ring_hom_sum.finset f],
  rw [finset.sum_congr rfl, (_ : @witt_polynomial p _ ℚ _ _ n -
    (finset.range n).sum (λ i, C p ^ i * X i ^ p ^ (n - i)) = C (p ^ n) * X n)],
  { rw [mul_right_comm, ← C_mul, mul_one_div_cancel, C_1, one_mul],
    exact pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt (nat.prime.pos ‹_›)) },
  { simp [witt_polynomial, nat.sub_self],
    rw is_semiring_hom.map_pow (@C ℚ ℕ _ _ _),
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
    -- erw from_W_to_X_basis_W_n p,
    -- refine X_in_terms_of_W_prop' p _ _ _ n,
}
end

-- lemma from_X_to_W_basis_comp_from_W_to_X_basis (f) :
--   from_X_to_W_basis p (from_W_to_X_basis p _ f) = f :=
-- begin
--   show (from_X_to_W_basis p ∘ from_W_to_X_basis p _) f = f,
--   apply mv_polynomial.is_id,
--   { apply_instance },
--   { intro r,
--     let : _ := _,
--     refine @rat.ring_hom_unique _ _ _ _ this (by apply_instance) r,
--     let F := (from_X_to_W_basis p ∘ from_W_to_X_basis p _),
--     change is_ring_hom (λ (r : ℚ), F (C r)),
--     show is_ring_hom (F ∘ C),
--     exact is_ring_hom.comp _ _ },
--   { intro n,
--     delta from_X_to_W_basis function.comp,
--     erw from_W_to_X_basis_W_n p,
--     refine X_in_terms_of_W_prop' p _ _ _ n, }
-- end

lemma X_in_terms_of_W_prop (n : ℕ) : (X_in_terms_of_W p n).eval₂ C (witt_polynomial p) = X n :=
begin
  letI : is_ring_hom (@C ℚ ℕ _ _ _) := by apply_instance,
  haveI H := @eval_witt_hom p _ ℚ _ _,
  have fC := eval₂_C C (@witt_polynomial p _ ℚ _ _),
  have fX := eval₂_X C (@witt_polynomial p _ ℚ _ _),
  revert H fC fX, generalize : eval₂ C (@witt_polynomial p _ ℚ _ _) = f,
  introsI, exact X_in_terms_of_W_prop' p f fC fX n
end

-- lemma from_X_to_W_basis_X_n (n) : from_X_to_W_basis p (witt_polynomial p n) = X n :=
-- by simp only [from_X_to_W_basis, eval₂_X, X_in_terms_of_W_prop]

def witt_structure_rat (Φ : mv_polynomial bool ℚ) : ℕ → mv_polynomial (bool × ℕ) ℚ :=
λ n, eval₂ C (λ k : ℕ,
   Φ.eval₂ C (λ b, ((witt_polynomial p k).eval (λ i, X (b,i))))
) (X_in_terms_of_W p n)

lemma X_in_terms_of_W_prop₂ (k : ℕ) : (witt_polynomial p k).eval₂ C (X_in_terms_of_W p) = X k :=
begin
  suffices :
  eval₂ C (X_in_terms_of_W p) ((C p)^k * X k) +
      eval₂ C (X_in_terms_of_W p) (finset.sum (finset.range k) (λ (i : ℕ), (C p)^i * (X i)^p^(k-i))) =
    X k,
  { simpa [witt_polynomial, finset.sum_range_succ] },
  rw is_ring_hom.map_mul (eval₂ C $ X_in_terms_of_W p),
  rw is_semiring_hom.map_pow (eval₂ C $ X_in_terms_of_W p),
  rw eval₂_C,
  rw eval₂_X,
  rw X_in_terms_of_W_eq,
  rw mul_comm,
  rw mul_assoc,
  rw ← is_semiring_hom.map_pow C,
  rw [← C_mul, one_div_mul_cancel, C_1, mul_one],
  { rw ring_hom_sum.finset (eval₂ C $ X_in_terms_of_W p),
    rw sub_add_eq_add_sub,
    apply sub_eq_of_eq_add',
    rw add_comm,
    rw function.comp,
    congr,
    funext i,
    rw is_ring_hom.map_mul (eval₂ C $ X_in_terms_of_W p),
    rw is_semiring_hom.map_pow (eval₂ C $ X_in_terms_of_W p),
    rw eval₂_C,
    rw is_semiring_hom.map_pow (eval₂ C $ X_in_terms_of_W p),
    rw eval₂_X,
    {apply_instance} },
  { refine pow_ne_zero _ (nat.cast_ne_zero.2 $ ne_of_gt _),
    apply nat.prime.pos,
    assumption },
  apply_instance
end

lemma eval₂_assoc
{S : Type*} [decidable_eq S] [comm_ring S]
{σ : Type*} [decidable_eq σ]
{τ : Type*} [decidable_eq τ]
{ι : Type*} [decidable_eq ι]
(φ : σ → mv_polynomial ι S)
(q : τ → mv_polynomial σ S)
(p : mv_polynomial τ S)
: eval₂ C (eval₂ C φ ∘ q) p = eval₂ C φ (eval₂ C q p)
:=
begin
  rw eval₂_comp_left (eval₂ C φ),
  congr, funext, simp,
end

theorem witt_structure_prop (Φ : mv_polynomial bool ℚ) (φ : ℕ → mv_polynomial (bool × ℕ) ℚ) :
  (((∀ (n : ℕ), (((witt_polynomial p n).eval₂ C φ) =
    (eval₂ C (λ b : bool, ((witt_polynomial p n).eval (λ i : ℕ, X (b,i)))) Φ)))
  ↔ (φ = witt_structure_rat p Φ)) : Prop) :=
begin
  split,
  { intro H,
    funext n,
    unfold witt_structure_rat,
    rw show φ n = ((X_in_terms_of_W p n).eval₂ C (witt_polynomial p)).eval₂ C φ,
    { rw [X_in_terms_of_W_prop p, eval₂_X] },
    rw ← eval₂_assoc,
    unfold function.comp,
    congr,
    funext k,
    exact H k },
  { intros H k,
    subst H,
    unfold witt_structure_rat,
    rw ← function.comp,
    rw eval₂_assoc,
    rw X_in_terms_of_W_prop₂ p k,
    rw eval₂_X }
end

def witt_structure_int (Φ : mv_polynomial bool ℤ) (n : ℕ) : mv_polynomial (bool × ℕ) ℤ :=
finsupp.map_range rat.num (rat.coe_int_num 0) (witt_structure_rat p (map int.cast Φ) n)

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
