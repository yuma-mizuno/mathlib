/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import order.well_founded_set
import algebra.big_operators.finprod
import ring_theory.valuation.basic
import algebra.module.pi
import ring_theory.power_series.basic

/-!
# Hahn Series

## Main Definitions
  * If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded.
  * If `R` is a (commutative) additive monoid or group, then so is `hahn_series Γ R`.
  * If `R` is a (comm_)(semi)ring, then so is `hahn_series Γ R`.
  * `hahn_series.add_val Γ R` defines an `add_valuation` on `hahn_series Γ R`.
  * A `hahn_series.summable_family` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `hahn_series.summable_family.hsum`, which can be bundled as a `linear_map` as
  `hahn_series.summable_family.lsum`. Note that this is different from `summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `hahn_series.summable_family`, and formally summable families whose sums do not converge
  topologically.

## TODO
  * Given `[linear_ordered_add_comm_group Γ]` and `[field R]`, define `field (hahn_series Γ R)`.
  * Build an API for the variable `X`
  * Define Laurent series

-/

open finset
open_locale big_operators classical
noncomputable theory

/-- If `Γ` is linearly ordered and `R` has zero, then `hahn_series Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure hahn_series (Γ : Type*) (R : Type*) [linear_order Γ] [has_zero R] :=
(coeff : Γ → R)
(is_wf_support' : (function.support coeff).is_wf)

variables {Γ : Type*} {R : Type*}

namespace hahn_series

section zero
variables [linear_order Γ] [has_zero R]

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
def support (x : hahn_series Γ R) : set Γ := function.support x.coeff

@[simp]
lemma is_wf_support (x : hahn_series Γ R) : x.support.is_wf := x.is_wf_support'

@[simp]
lemma mem_support (x : hahn_series Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 := iff.refl _

instance : has_zero (hahn_series Γ R) :=
⟨{ coeff := 0,
   is_wf_support' := by simp }⟩

instance : inhabited (hahn_series Γ R) := ⟨0⟩

instance [subsingleton R] : subsingleton (hahn_series Γ R) :=
⟨λ a b, a.ext b (subsingleton.elim _ _)⟩

@[simp]
lemma zero_coeff {a : Γ} : (0 : hahn_series Γ R).coeff a = 0 := rfl

@[simp]
lemma support_zero : support (0 : hahn_series Γ R) = ∅ := function.support_zero

@[simp]
lemma support_nonempty_iff {x : hahn_series Γ R} :
  x.support.nonempty ↔ x ≠ 0 :=
begin
  split,
  { rintro ⟨a, ha⟩ rfl,
    apply ha zero_coeff },
  { contrapose!,
    rw set.not_nonempty_iff_eq_empty,
    intro h,
    ext a,
    have ha := set.not_mem_empty a,
    rw [← h, mem_support, not_not] at ha,
    rw [ha, zero_coeff] }
end

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : zero_hom R (hahn_series Γ R) :=
{ to_fun := λ r, { coeff := pi.single a r,
    is_wf_support' := (set.is_wf_singleton a).mono pi.support_single_subset },
  map_zero' := ext _ _ (pi.single_zero _) }

variables {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r := pi.single_eq_same a r

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := pi.single_eq_of_ne h r

theorem single_coeff : (single a r).coeff b = if (b = a) then r else 0 :=
by { split_ifs with h; simp [h] }

@[simp]
lemma support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
pi.support_single_of_ne h

lemma support_single_subset : support (single a r) ⊆ {a} :=
pi.support_single_subset

lemma eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
support_single_subset h

@[simp]
lemma single_eq_zero : (single a (0 : R)) = 0 := (single a).map_zero

instance [nonempty Γ] [nontrivial R] : nontrivial (hahn_series Γ R) :=
⟨begin
  obtain ⟨r, s, rs⟩ := exists_pair_ne R,
  inhabit Γ,
  refine ⟨single (arbitrary Γ) r, single (arbitrary Γ) s, λ con, rs _⟩,
  rw [← single_coeff_same (arbitrary Γ) r, con, single_coeff_same],
end⟩

lemma coeff_min_ne_zero {x : hahn_series Γ R} (hx : x ≠ 0) :
  x.coeff (x.is_wf_support.min (support_nonempty_iff.2 hx)) ≠ 0 :=
x.is_wf_support.min_mem (support_nonempty_iff.2 hx)

end zero

section addition

variable [linear_order Γ]

section add_monoid
variable [add_monoid R]

instance : has_add (hahn_series Γ R) :=
{ add := λ x y, { coeff := x.coeff + y.coeff,
                  is_wf_support' := (x.is_wf_support.union y.is_wf_support).mono
                    (function.support_add _ _) } }

instance : add_monoid (hahn_series Γ R) :=
{ zero := 0,
  add := (+),
  add_assoc := λ x y z, by { ext, apply add_assoc },
  zero_add := λ x, by { ext, apply zero_add },
  add_zero := λ x, by { ext, apply add_zero } }

@[simp]
lemma add_coeff' {x y : hahn_series Γ R} :
  (x + y).coeff = x.coeff + y.coeff := rfl

lemma add_coeff {x y : hahn_series Γ R} {a : Γ} :
  (x + y).coeff a = x.coeff a + y.coeff a := rfl

lemma support_add_subset {x y : hahn_series Γ R} :
  support (x + y) ⊆ support x ∪ support y :=
λ a ha, begin
  rw [mem_support, add_coeff] at ha,
  rw [set.mem_union, mem_support, mem_support],
  contrapose! ha,
  rw [ha.1, ha.2, add_zero],
end

/-- `single` as an additive monoid/group homomorphism -/
@[simps] def single.add_monoid_hom (a : Γ) : R →+ (hahn_series Γ R) :=
{ map_add' := λ x y, by { ext b, by_cases h : b = a; simp [h] },
  ..single a }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps] def coeff.add_monoid_hom (g : Γ) : (hahn_series Γ R) →+ R :=
{ to_fun := λ f, f.coeff g,
  map_zero' := zero_coeff,
  map_add' := λ x y, add_coeff }

end add_monoid

instance [add_comm_monoid R] : add_comm_monoid (hahn_series Γ R) :=
{ add_comm := λ x y, by { ext, apply add_comm }
  .. hahn_series.add_monoid }

section add_group
variable [add_group R]

instance : add_group (hahn_series Γ R) :=
{ neg := λ x, { coeff := λ a, - x.coeff a,
                is_wf_support' := by { rw function.support_neg,
                  exact x.is_wf_support }, },
  add_left_neg := λ x, by { ext, apply add_left_neg },
  .. hahn_series.add_monoid }

@[simp]
lemma neg_coeff' {x : hahn_series Γ R} : (- x).coeff = - x.coeff := rfl

lemma neg_coeff {x : hahn_series Γ R} {a : Γ} : (- x).coeff a = - x.coeff a := rfl

@[simp]
lemma support_neg {x : hahn_series Γ R} : (- x).support = x.support :=
by { ext, simp }

@[simp]
lemma sub_coeff' {x y : hahn_series Γ R} :
  (x - y).coeff = x.coeff - y.coeff := by { ext, simp [sub_eq_add_neg] }

lemma sub_coeff {x y : hahn_series Γ R} {a : Γ} :
  (x - y).coeff a = x.coeff a - y.coeff a := by simp

end add_group

instance [add_comm_group R] : add_comm_group (hahn_series Γ R) :=
{ .. hahn_series.add_comm_monoid,
  .. hahn_series.add_group }

end addition

section distrib_mul_action
variables [linear_order Γ] {V : Type*} [monoid R] [add_monoid V] [distrib_mul_action R V]

instance : has_scalar R (hahn_series Γ V) :=
⟨λ r x, { coeff := r • x.coeff,
          is_wf_support' := x.is_wf_support.mono (function.support_smul_subset_right r x.coeff) }⟩

@[simp]
lemma smul_coeff {r : R} {x : hahn_series Γ V} {a : Γ} : (r • x).coeff a = r • (x.coeff a) := rfl

instance : distrib_mul_action R (hahn_series Γ V) :=
{ smul := (•),
  one_smul := λ _, by { ext, simp },
  smul_zero := λ _, by { ext, simp },
  smul_add := λ _ _ _, by { ext, simp [smul_add] },
  mul_smul := λ _ _ _, by { ext, simp [mul_smul] } }

variables {S : Type*} [monoid S] [distrib_mul_action S V]

instance [has_scalar R S] [is_scalar_tower R S V] :
  is_scalar_tower R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp }⟩

instance [smul_comm_class R S V] :
  smul_comm_class R S (hahn_series Γ V) :=
⟨λ r s a, by { ext, simp [smul_comm] }⟩

end distrib_mul_action

section semimodule
variables [linear_order Γ] [semiring R] {V : Type*} [add_comm_monoid V] [semimodule R V]

instance : semimodule R (hahn_series Γ V) :=
{ zero_smul := λ _, by { ext, simp },
  add_smul := λ _ _ _, by { ext, simp [add_smul] },
  .. hahn_series.distrib_mul_action }

/-- `single` as a linear map -/
@[simps] def single.linear_map (a : Γ) : R →ₗ[R] (hahn_series Γ R) :=
{ map_smul' := λ r s, by { ext b, by_cases h : b = a; simp [h] },
  ..single.add_monoid_hom a }

/-- `coeff g` as a linear map -/
@[simps] def coeff.linear_map (g : Γ) : (hahn_series Γ R) →ₗ[R] R :=
{ map_smul' := λ r s, rfl,
  ..coeff.add_monoid_hom g }

end semimodule

section multiplication

variable [linear_ordered_cancel_add_comm_monoid Γ]

instance [has_zero R] [has_one R] : has_one (hahn_series Γ R) :=
⟨single 0 1⟩

@[simp]
lemma one_coeff [has_zero R] [has_one R] {a : Γ} :
  (1 : hahn_series Γ R).coeff a = if a = 0 then 1 else 0 := single_coeff

@[simp]
lemma single_zero_one [has_zero R] [has_one R] : (single 0 (1 : R)) = 1 := rfl

@[simp]
lemma support_one [semiring R] [nontrivial R] :
  support (1 : hahn_series Γ R) = {0} :=
support_single_of_ne one_ne_zero

instance [semiring R] : has_mul (hahn_series Γ R) :=
{ mul := λ x y, { coeff := λ a,
    ∑ᶠ ij ∈ (set.add_antidiagonal' a), x.coeff (prod.fst ij) * y.coeff (prod.snd ij),
    is_wf_support' := begin
      refine (x.is_wf_support.add y.is_wf_support).mono (λ a ha, _),
      obtain ⟨⟨i,j⟩, hij1, hij2⟩ := exists_ne_zero_of_finsum_mem_ne_zero ha,
      obtain ⟨hi, hj⟩ := ne_zero_and_ne_zero_of_mul hij2,
      exact ⟨i, j, hi, hj, hij1⟩,
    end, }, }

@[simp]
lemma mul_coeff [semiring R] {x y : hahn_series Γ R} {a : Γ} :
  (x * y).coeff a = ∑ᶠ ij ∈ (set.add_antidiagonal' a),
    x.coeff (prod.fst ij) * y.coeff ij.snd := rfl

lemma mul_coeff_eq_sum [semiring R] {x y : hahn_series Γ R} {a : Γ} (s : finset (Γ × Γ))
  (hs1 : ∀ i j : Γ, (i,j) ∈ s → i + j = a)
  (hs2 : ∀ i j : Γ, i + j = a → x.coeff i ≠ 0 → y.coeff j ≠ 0 → (i,j) ∈ s) :
  (x * y).coeff a = ∑ ij in s, x.coeff (prod.fst ij) * y.coeff ij.snd :=
begin
  rw [mul_coeff, finsum_mem_eq_sum_of_subset],
  { rintros ⟨i, j⟩ ⟨hij, hihj⟩,
    obtain ⟨hi, hj⟩ := ne_zero_and_ne_zero_of_mul hihj,
    exact hs2 i j hij hi hj },
  { rintros ⟨i, j⟩ hij,
    exact hs1 i j (finset.mem_coe.2 hij) }
end

lemma foo [semiring R] (x y : hahn_series Γ R) (a : Γ) :
  ((set.add_antidiagonal' a) ∩
    (function.support (λ (i : Γ × Γ), x.coeff i.fst * y.coeff i.snd))).finite := sorry

instance [semiring R] : distrib (hahn_series Γ R) :=
{ left_distrib := λ x y z, begin
    ext a,
    simp only [mul_add, mul_coeff, pi.add_apply, add_coeff'],
    exact finsum_mem_add_distrib' (foo x y a) (foo x z a),
  end,
  right_distrib := λ x y z, begin
    ext a,
    simp only [add_mul, mul_coeff, pi.add_apply, add_coeff'],
    exact finsum_mem_add_distrib' (foo x z a) (foo y z a),
  end,
  .. hahn_series.has_mul,
  .. hahn_series.has_add }

lemma single_mul_coeff_add [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} {b : Γ} :
  ((single b r) * x).coeff (a + b) = r * x.coeff a :=
begin
  rw [add_comm, mul_coeff_eq_sum {(b, a)}, sum_singleton, single_coeff_same],
  { intros i j hij,
    obtain ⟨rfl, rfl⟩ := finset.mem_singleton.1 hij,
    refl },
  { intros i j hij hi hj,
    rw finset.mem_singleton,
    have ib : i = b,
    { contrapose! hi,
      exact single_coeff_of_ne hi },
    subst ib,
    exact congr rfl (add_left_cancel hij) },
end

lemma mul_single_coeff_add [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} {b : Γ} :
  (x * (single b r)).coeff (a + b) = x.coeff a * r :=
begin
  rw [mul_coeff_eq_sum {(a, b)}, sum_singleton, single_coeff_same],
  { intros i j hij,
    obtain ⟨rfl, rfl⟩ := finset.mem_singleton.1 hij,
    refl },
  { intros i j hij hi hj,
    rw finset.mem_singleton,
    have jb : j = b,
    { contrapose! hj,
      exact single_coeff_of_ne hj },
    subst jb,
    exact congr (congr rfl (add_right_cancel hij)) rfl },
end

@[simp]
lemma mul_single_zero_coeff [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} :
  (x * (single 0 r)).coeff a = x.coeff a * r  :=
by rw [← add_zero a, mul_single_coeff_add, add_zero]

lemma single_zero_mul_coeff [semiring R] {r : R} {x : hahn_series Γ R} {a : Γ} :
  ((single 0 r) * x).coeff a = r * x.coeff a :=
by rw [← add_zero a, single_mul_coeff_add, add_zero]

@[simp]
lemma single_zero_mul_eq_smul [semiring R] {r : R} {x : hahn_series Γ R} :
  (single 0 r) * x = r • x :=
by { ext, exact single_zero_mul_coeff }

theorem support_mul_subset_add_support [semiring R] {x y : hahn_series Γ R} :
  support (x * y) ⊆ support x + support y :=
begin
  intros a ha,
  obtain ⟨⟨i,j⟩, hij1, hij2⟩ := exists_ne_zero_of_finsum_mem_ne_zero ha,
  obtain ⟨hi, hj⟩ := ne_zero_and_ne_zero_of_mul hij2,
  exact ⟨i, j, hi, hj, hij1⟩,
end

@[simp]
lemma mul_coeff_min_add_min [semiring R] {x y : hahn_series Γ R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (x * y).coeff (x.is_wf_support.min (support_nonempty_iff.2 hx) +
    y.is_wf_support.min (support_nonempty_iff.2 hy)) =
    (x.coeff (x.is_wf_support.min (support_nonempty_iff.2 hx))) *
    y.coeff (y.is_wf_support.min (support_nonempty_iff.2 hy)) :=
begin
  rw [mul_coeff_eq_sum {((x.is_wf_support.min _, y.is_wf_support.min _))}, finset.sum_singleton],
  { intros i j hij,
    obtain ⟨rfl, rfl⟩ := finset.mem_singleton.1 hij,
    refl },
  { intros i j hij hi hj,
    cases eq_or_lt_of_le ((x.is_wf_support.min_le _ hi)) with heq hlt,
    { rw [mem_singleton, prod.mk.inj_iff],
      rw heq at hij,
      exact ⟨heq.symm, add_left_cancel hij⟩ },
    { contrapose hij,
      exact ne_of_gt (add_lt_add_of_lt_of_le hlt (y.is_wf_support.min_le _ hj)) } },
end

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[to_additive "Sum over a sigma type equals the sum of fiberwise sums. For rewriting
in the reverse direction, use `finset.sum_sigma'`"]
lemma finprod_mem_sigma {α β : Type*} [comm_monoid β] {σ : α → Type*}
  (s : set α) (t : Πa, set (σ a)) (f : sigma σ → β)
  (hs : (s ∩ { a | ∃ b ∈ t a, f ⟨a, b⟩ ≠ 1 }).finite)
  (ht : ∀ a, a ∈ s → (t a ∩ function.mul_support (λ b, f ⟨a, b⟩)).finite) :
  ∏ᶠ x ∈ { x : Σ a : α, σ a | x.1 ∈ s ∧ x.2 ∈ t x.1 }, f x = ∏ᶠ a ∈ s, ∏ᶠ s ∈ (t a), f ⟨a, s⟩ :=
begin
  rw [finprod_mem_eq_prod_of_subset, finset.prod_sigma hs.to_finset (λ a,
      if has : a ∈ s then (ht a has).to_finset else ∅),
    finprod_mem_eq_prod_of_subset, finset.prod_congr rfl (λ a ha, _)],
  { rw finprod_mem_eq_prod _ (ht a (hs.mem_to_finset.1 ha).1),
    rw finset.prod_congr (dif_pos _),
    intros b hb,
    refl },
  { rw [set.finite.coe_to_finset],
    rintro x ⟨h1, h2⟩,
    refine set.mem_inter h1 _,
    simp only [exists_prop, ne.def, set.mem_set_of_eq],
    contrapose! h2,
    simp only [not_not, function.mem_mul_support, finprod_mem_congr rfl h2, finprod_one] },
  { rw [set.finite.coe_to_finset],
    apply set.inter_subset_left },
  { rintro ⟨a, b⟩ ⟨⟨h1, h2⟩, h3⟩,
    rw [finset.mem_coe, finset.mem_sigma, set.finite.mem_to_finset, dif_pos h1,
      set.finite.mem_to_finset],
    exact ⟨⟨h1, ⟨b, h2, h3⟩⟩, h2, h3⟩ },
  { rintro ⟨a, b⟩ h,
    rw [finset.mem_coe, finset.mem_sigma, set.finite.mem_to_finset, set.mem_inter_iff] at h,
    obtain ⟨⟨ha, h1⟩, hb⟩ := h,
    rw [dif_pos ha, set.finite.mem_to_finset, set.mem_inter_iff] at hb,
    exact ⟨ha, hb.1⟩ }
end

@[to_additive]
lemma finprod_mem_sigma' {α β : Type*} [comm_monoid β] {σ : α → Type*}
  (s : set α) (t : Πa, set (σ a)) (f : Πa, σ a → β)
  (hs : (s ∩ { a | ∃ b ∈ t a, f a b ≠ 1 }).finite)
  (ht : ∀ a, a ∈ s → (t a ∩ function.mul_support (λ b, f a b)).finite) :
  ∏ᶠ a ∈ s, ∏ᶠ x ∈ (t a), f a x = ∏ᶠ x ∈ { x : Σ a : α, σ a | x.1 ∈ s ∧ x.2 ∈ t x.1 }, f x.1 x.2 :=
eq.symm $ finprod_mem_sigma s t (λ x, f x.1 x.2) hs ht

/-- Product over a sigma type equals the product of fiberwise products. For rewriting
in the reverse direction, use `finset.prod_sigma'`.  -/
@[to_additive finsum_mem_prod "Sum over a sigma type equals the sum of fiberwise sums. For rewriting
in the reverse direction, use `finset.sum_sigma'`"]
lemma finprod_mem_prod {α β M : Type*} [comm_monoid M]
  (s : set α) (t : set β) (f : α × β → M)
  (h : (s.prod t ∩ function.mul_support f).finite) :
  ∏ᶠ x ∈ s.prod t, f x = ∏ᶠ a ∈ s, ∏ᶠ b ∈ t, f ⟨a, b⟩ :=
begin
  have hi : (s.prod t).inj_on prod.to_sigma,
  { rintro ⟨a, b⟩ _ ⟨c, d⟩ _ h,
    simp only [prod.to_sigma, heq_iff_eq] at h,
    rw [h.1, h.2] },
  refine (finprod_mem_congr rfl _).trans ((finprod_mem_image hi).symm.trans _),
  { exact λ ab, f ⟨ab.1, ab.2⟩ },
  { rintros ⟨a, b⟩ _,
    simp },
  refine (finprod_mem_congr _ (λ _ _, rfl)).trans ((finprod_mem_sigma s (λ _, t) _ _ _).trans _),
  { ext,
    simp only [set.mem_image, prod.to_sigma, set.mem_prod, set.mem_set_of_eq, prod.exists],
    refine ⟨_, λ h, ⟨x.fst, x.snd, h, by simp⟩⟩,
    rintro ⟨a, b, h, rfl⟩,
    exact h },
  { apply (h.image prod.fst).subset,
    rintros a ⟨hs, b, ht, h1⟩,
    exact ⟨⟨a, b⟩, ⟨⟨hs, ht⟩, h1⟩, rfl⟩ },
  { intros a ha,
    apply (h.image prod.snd).subset,
    rintros b ⟨hb, h'⟩,
    exact ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, h'⟩, rfl⟩ },
  { exact (finprod_mem_congr rfl (λ a ha, (finprod_mem_congr rfl (λ b hb, rfl)))) }
end

@[to_additive finsum_mem_prod']
lemma finprod_mem_prod' {α β M : Type*} [comm_monoid M]
  (s : set α) (t : set β) (f : α → β → M)
  (h : (s.prod t ∩ function.mul_support (function.uncurry f)).finite) :
  ∏ᶠ a ∈ s, ∏ᶠ b ∈ t, f a b = ∏ᶠ x ∈ s.prod t, f (prod.fst x) x.2 :=
eq.symm $ finprod_mem_prod s t (λ x, f x.1 x.2) h

lemma mul_finsum {α β : Type*} [semiring β] {f : α → β} {b : β} (h : (function.support f).finite) :
  b * (∑ᶠ x, f x) = ∑ᶠ x, b * f x :=
begin
  rw [finsum_eq_sum _ h, finset.mul_sum, finsum_eq_sum_of_support_subset],
  rw [set.finite.coe_to_finset],
  exact λ x, right_ne_zero_of_mul
end

lemma finsum_mul {α β : Type*} [semiring β] {f : α → β} {b : β} (h : (function.support f).finite) :
  (∑ᶠ x, f x) * b = ∑ᶠ x, f x * b :=
begin
  rw [finsum_eq_sum _ h, finset.sum_mul, finsum_eq_sum_of_support_subset],
  rw [set.finite.coe_to_finset],
  exact λ x, left_ne_zero_of_mul
end

lemma mul_finsum_mem {α β : Type*} [semiring β] {f : α → β} {b : β} {s : set α}
  (h : (s ∩ (function.support f)).finite) :
  b * (∑ᶠ x ∈ s, f x) = ∑ᶠ x ∈ s, b * f x :=
begin
  rw [finsum_mem_def, mul_finsum, finsum_mem_def, finsum_congr],
  { intro a,
    rw [set.indicator_apply, set.indicator_apply],
    split_ifs,
    { refl },
    { rw mul_zero } },
  { convert h,
    ext,
    simp }
end

lemma finsum_mem_mul {α β : Type*} [semiring β] {f : α → β} {b : β} {s : set α}
  (h : (s ∩ (function.support f)).finite) :
  (∑ᶠ x ∈ s, f x) * b = ∑ᶠ x ∈ s, f x * b :=
begin
  rw [finsum_mem_def, finsum_mul, finsum_mem_def, finsum_congr],
  { intro a,
    rw [set.indicator_apply, set.indicator_apply],
    split_ifs,
    { refl },
    { rw zero_mul } },
  { convert h,
    ext,
    simp }
end

private lemma mul_assoc' [semiring R] (x y z : hahn_series Γ R) :
  x * y * z = x * (y * z) :=
begin
  ext b,
  simp only [mul_coeff, mul_assoc],
  refine eq.trans (finsum_mem_congr rfl (λ ij hij, finsum_mem_mul _))
    (eq.trans _ (eq.symm (finsum_mem_congr rfl (λ ij hij, (mul_finsum_mem _))))),
  { sorry,

  },
  swap, sorry,
  refine ((finsum_mem_sigma' _ _ _ _ _).trans _).trans (finsum_mem_sigma' _ _ _ _ _).symm,
  sorry, sorry,
  swap, sorry, swap, sorry,
  refine finsum_mem_eq_of_bij_on (λ q : Σ (a : Γ × Γ), Γ × Γ, (⟨⟨q.2.1, q.2.2 + q.1.2⟩,
    q.2.2, q.1.2⟩ : Σ (a : Γ × Γ), Γ × Γ)) ⟨_, _, _⟩ _,
  { simp only [set.mem_add_antidiagonal'],
    rintro ⟨⟨i, j⟩, k, l⟩ ⟨rfl, h2⟩,
    dsimp only at h2,
    obtain rfl := h2,
    exact ⟨(add_assoc _ _ _).symm, rfl⟩ },
  { rintros ⟨⟨i, j⟩, k, l⟩ ⟨h11, h12⟩ ⟨⟨i', j'⟩, k', l'⟩ h2 h3,
    simp only [heq_iff_eq, set.mem_add_antidiagonal', set.mem_set_of_eq] at *,
    subst h12,
    obtain ⟨rfl, rfl⟩ := h2,
    simp only [prod.ext_iff] at h3,
    obtain ⟨⟨rfl, h31⟩, rfl, rfl⟩ := h3,
    exact ⟨rfl, rfl⟩ },
  { rintro ⟨⟨i, j⟩, k, l⟩ ⟨h1, h2⟩,
    simp only [set.mem_image, set.mem_add_antidiagonal', prod.mk.inj_iff, sigma.exists,
      set.mem_set_of_eq, heq_iff_eq, prod.exists],
    simp only [set.mem_add_antidiagonal'] at h1 h2,
    rw [← h2, ← add_assoc] at h1,
    exact ⟨_, _, _, _, ⟨h1, rfl⟩, ⟨rfl, h2⟩, rfl, rfl⟩ },
  { rintros ⟨⟨i, j⟩, k, l⟩ ⟨h1, h2⟩, refl }
end

instance [semiring R] : semiring (hahn_series Γ R) :=
{ zero := 0,
  one := 1,
  add := (+),
  mul := (*),
  zero_mul := λ _, by { ext, simp },
  mul_zero := λ _, by { ext, simp },
  one_mul := λ x, single_zero_mul_eq_smul.trans (one_smul _ _),
  mul_one := λ x, by { ext, exact mul_single_zero_coeff.trans (mul_one _) },
  mul_assoc := mul_assoc',
  .. hahn_series.add_comm_monoid,
  .. hahn_series.distrib }

instance [comm_semiring R] : comm_semiring (hahn_series Γ R) :=
{ mul_comm := λ x y, begin
    ext,
    simp_rw [mul_coeff, mul_comm],
    refine finsum_mem_eq_of_bij_on (λ ⟨i, j⟩, ⟨j, i⟩) ⟨_, _, _⟩ (λ ⟨_,_⟩ _, rfl),
    { rintro ⟨i,j⟩ hi,
      exact eq.trans (add_comm _ _) hi },
    { rintros ⟨a1, a2⟩ ha ⟨b1, b2⟩ hb hab,
      rw prod.ext_iff at *,
      refine ⟨hab.2, hab.1⟩ },
    { rintro ⟨i,j⟩ hi,
      simp only [set.mem_image, set.mem_add_antidiagonal', prod.exists],
      refine ⟨_, _, eq.trans (add_comm _ _) hi, rfl⟩, },
  end,
  .. hahn_series.semiring }

instance [ring R] : ring (hahn_series Γ R) :=
{ .. hahn_series.semiring,
  .. hahn_series.add_comm_group }

instance [comm_ring R] : comm_ring (hahn_series Γ R) :=
{ .. hahn_series.comm_semiring,
  .. hahn_series.ring }

instance [integral_domain R] : integral_domain (hahn_series Γ R) :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y xy, begin
    by_cases hx : x = 0,
    { left, exact hx },
    right,
    contrapose! xy,
    rw [hahn_series.ext_iff, function.funext_iff, not_forall],
    refine ⟨x.is_wf_support.min (support_nonempty_iff.2 hx) +
      y.is_wf_support.min (support_nonempty_iff.2 xy), _⟩,
    rw [mul_coeff_min_add_min, zero_coeff, mul_eq_zero],
    simp [coeff_min_ne_zero, hx, xy],
  end,
  .. hahn_series.nontrivial,
  .. hahn_series.comm_ring }

@[to_additive] lemma finprod_mem_comm' {α β M : Type*} [comm_monoid M] {s : set α} {t : set β}
  (f : α → β → M)
  (h : ((s.prod t) ∩ function.mul_support (function.uncurry f)).finite) :
  ∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j :=
begin
  rw [finprod_mem_prod' _ _ _ h, finprod_mem_prod', finprod_mem_eq_of_bij_on prod.swap ⟨_, _, _⟩],
  { rintros ⟨a, b⟩ _,
    refl },
  { rintros ⟨a, b⟩ ⟨ha, hb⟩,
    exact ⟨hb, ha⟩ },
  { rintros ⟨a1, b1⟩ _ ⟨a2, b2⟩ _ h,
    rw [prod.swap_prod_mk, prod.swap_prod_mk] at h,
    obtain ⟨rfl, rfl⟩ := h,
    refl },
  { rintros ⟨b, a⟩ ⟨hb, ha⟩,
    exact ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩ },
  { apply (h.image prod.swap).subset,
    rintros ⟨b, a⟩ ⟨⟨hb, ha⟩, h⟩,
    exact ⟨⟨a, b⟩, ⟨⟨ha, hb⟩, h⟩, rfl⟩ }
end

section semiring
variables [semiring R]

@[simp]
lemma single_mul_single {a b : Γ} {r s : R} :
  single a r * single b s = single (a + b) (r * s) :=
begin
  ext x,
  by_cases h : x = a + b,
  { rw [h, mul_single_coeff_add],
    simp },
  { rw [single_coeff_of_ne h, mul_coeff, finsum_mem_congr rfl, finsum_mem_zero],
    rintros ⟨y1, y2⟩ hy,
    obtain rfl := set.mem_add_antidiagonal'.1 hy,
    contrapose! h,
    obtain ⟨hy1, hy2⟩ := ne_zero_and_ne_zero_of_mul h,
    rw [eq_of_mem_support_single hy1, eq_of_mem_support_single hy2] }
end

/-- `C a` is the constant Hahn Series `a`. `C` is provided as a ring homomorphism. -/
@[simps] def C : R →+* (hahn_series Γ R) :=
{ to_fun := single 0,
  map_zero' := single_eq_zero,
  map_one' := rfl,
  map_add' := λ x y, by { ext a, by_cases h : a = 0; simp [h] },
  map_mul' := λ x y, by rw [single_mul_single, zero_add] }

@[simp]
lemma C_zero : C (0 : R) = (0 : hahn_series Γ R) := C.map_zero

@[simp]
lemma C_one : C (1 : R) = (1 : hahn_series Γ R) := C.map_one

lemma C_mul_eq_smul {r : R} {x : hahn_series Γ R} : C r * x = r • x :=
single_zero_mul_eq_smul

end semiring

section algebra
variables [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

instance : algebra R (hahn_series Γ A) :=
{ to_ring_hom := C.comp (algebra_map R A),
  smul_def' := λ r x, by { ext, simp },
  commutes' := λ r x, by { ext, simp only [smul_coeff, single_zero_mul_eq_smul, ring_hom.coe_comp,
    ring_hom.to_fun_eq_coe, C_apply, function.comp_app, algebra_map_smul, mul_single_zero_coeff],
    rw [← algebra.commutes, algebra.smul_def], }, }

theorem C_eq_algebra_map : C = (algebra_map R (hahn_series Γ R)) := rfl

theorem algebra_map_apply {r : R} :
  algebra_map R (hahn_series Γ A) r = C (algebra_map R A r) := rfl

instance [nontrivial Γ] [nontrivial R] : nontrivial (subalgebra R (hahn_series Γ R)) :=
⟨⟨⊥, ⊤, begin
  rw [ne.def, set_like.ext_iff, not_forall],
  obtain ⟨a, ha⟩ := exists_ne (0 : Γ),
  refine ⟨single a 1, _⟩,
  simp only [algebra.mem_bot, not_exists, set.mem_range, iff_true, algebra.mem_top],
  intros x,
  rw [ext_iff, function.funext_iff, not_forall],
  refine ⟨a, _⟩,
  rw [single_coeff_same, algebra_map_apply, C_apply, single_coeff_of_ne ha],
  exact zero_ne_one
end⟩⟩

end algebra

end multiplication

section semiring
variables [semiring R]

/-- The ring `hahn_series ℕ R` is isomorphic to `power_series R`. -/
@[simps] def to_power_series : (hahn_series ℕ R) ≃+* power_series R :=
{ to_fun := λ f, power_series.mk f.coeff,
  inv_fun := λ f, ⟨λ n, power_series.coeff R n f, nat.lt_wf.is_wf _⟩,
  left_inv := λ f, by { ext, simp },
  right_inv := λ f, by { ext, simp },
  map_add' := λ f g, by { ext, simp },
  map_mul' := λ f g, begin
    ext n,
    simp only [power_series.coeff_mul, power_series.coeff_mk, mul_coeff, is_wf_support],
    apply finsum_mem_eq_sum_of_subset,
    { rintro _ ⟨h1, h2⟩,
      rw [mem_coe, nat.mem_antidiagonal],
      exact h1 },
    { intros _ h,
      rwa [mem_coe, nat.mem_antidiagonal] at h },
  end }

lemma coeff_to_power_series {f : hahn_series ℕ R} {n : ℕ} :
  power_series.coeff R n f.to_power_series = f.coeff n :=
power_series.coeff_mk _ _

lemma coeff_to_power_series_symm {f : power_series R} {n : ℕ} :
  (hahn_series.to_power_series.symm f).coeff n = power_series.coeff R n f := rfl

end semiring

section algebra
variables (R) [comm_semiring R] {A : Type*} [semiring A] [algebra R A]

/-- The `R`-algebra `hahn_series ℕ A` is isomorphic to `power_series A`. -/
@[simps] def to_power_series_alg : (hahn_series ℕ A) ≃ₐ[R] power_series A :=
{ commutes' := λ r, begin
    ext n,
    simp only [algebra_map_apply, power_series.algebra_map_apply, ring_equiv.to_fun_eq_coe, C_apply,
      coeff_to_power_series],
    cases n,
    { simp only [power_series.coeff_zero_eq_constant_coeff, single_coeff_same],
      refl },
    { simp only [n.succ_ne_zero, ne.def, not_false_iff, single_coeff_of_ne],
      rw [power_series.coeff_C, if_neg n.succ_ne_zero] }
  end,
  .. to_power_series }

end algebra

section valuation

variables [linear_ordered_add_comm_group Γ] [integral_domain R] [nontrivial R]

instance : linear_ordered_comm_group (multiplicative Γ) :=
{ .. (infer_instance : linear_order (multiplicative Γ)),
  .. (infer_instance : ordered_comm_group (multiplicative Γ)) }

instance : linear_ordered_comm_group_with_zero (with_zero (multiplicative Γ)) :=
{ zero_le_one := with_zero.zero_le 1,
  .. (with_zero.ordered_comm_monoid),
  .. (infer_instance : linear_order (with_zero (multiplicative Γ))),
  .. (infer_instance : comm_group_with_zero (with_zero (multiplicative Γ))) }

variables (Γ) (R)

/-- The additive valuation on `hahn_series Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def add_val : add_valuation (hahn_series Γ R) (with_top Γ) :=
add_valuation.of (λ x, if h : x = (0 : hahn_series Γ R) then (⊤ : with_top Γ)
    else x.is_wf_support.min (support_nonempty_iff.2 h))
  (dif_pos rfl)
  ((dif_neg one_ne_zero).trans (by simp))
  (λ x y, begin
    by_cases hx : x = 0,
    { by_cases hy : y = 0; { simp [hx, hy] } },
    { by_cases hy : y = 0,
      { simp [hx, hy] },
      { simp only [hx, hy, support_nonempty_iff, dif_neg, not_false_iff, is_wf_support, min_le_iff],
        by_cases hxy : x + y = 0,
        { simp [hxy] },
        rw [dif_neg hxy, with_top.coe_le_coe, with_top.coe_le_coe, ← min_le_iff,
          ← set.is_wf.min_union],
        exact set.is_wf.min_le_min_of_subset support_add_subset, } },
  end)
  (λ x y, begin
    by_cases hx : x = 0,
    { simp [hx] },
    by_cases hy : y = 0,
    { simp [hy] },
    rw [dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy),
      ← with_top.coe_add, with_top.coe_eq_coe],
    apply le_antisymm,
    { apply set.is_wf.min_le,
      rw [mem_support, mul_coeff_min_add_min],
      exact mul_ne_zero (coeff_min_ne_zero hx) (coeff_min_ne_zero hy) },
    { rw ← set.is_wf.min_add,
      exact set.is_wf.min_le_min_of_subset (support_mul_subset_add_support) },
  end)

variables {Γ} {R}

lemma add_val_apply {x : hahn_series Γ R} :
  add_val Γ R x = if h : x = (0 : hahn_series Γ R) then (⊤ : with_top Γ)
    else x.is_wf_support.min (support_nonempty_iff.2 h) :=
add_valuation.of_apply _

@[simp]
lemma add_val_apply_of_ne {x : hahn_series Γ R} (hx : x ≠ 0) :
  add_val Γ R x = x.is_wf_support.min (support_nonempty_iff.2 hx) :=
dif_neg hx

end valuation

section
variables (Γ) (R) [linear_order Γ] [add_comm_monoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
structure summable_family (α : Type*) :=
(to_fun : α → hahn_series Γ R)
(is_wf_Union_support' : set.is_wf (⋃ (a : α), (to_fun a).support))
(finite_co_support' : ∀ (g : Γ), {a | (to_fun a).coeff g ≠ 0}.finite)

end

namespace summable_family
section add_comm_monoid

variables [linear_order Γ] [add_comm_monoid R] {α : Type*}

instance : has_coe_to_fun (summable_family Γ R α) :=
⟨λ _, (α → hahn_series Γ R), to_fun⟩

lemma is_wf_Union_support (s : summable_family Γ R α) : set.is_wf (⋃ (a : α), (s a).support) :=
s.is_wf_Union_support'

lemma finite_co_support (s : summable_family Γ R α) (g : Γ) :
  (function.support (λ a, (s a).coeff g)).finite :=
s.finite_co_support' g

lemma coe_injective : @function.injective (summable_family Γ R α) (α → hahn_series Γ R) coe_fn
| ⟨f1, hU1, hf1⟩ ⟨f2, hU2, hf2⟩ h :=
begin
  change f1 = f2 at h,
  subst h,
end

@[ext]
lemma ext {s t : summable_family Γ R α} (h : ∀ (a : α), s a = t a) : s = t :=
coe_injective $ funext h

instance : has_add (summable_family Γ R α) :=
⟨λ x y, { to_fun := x + y,
    is_wf_Union_support' := (x.is_wf_Union_support.union y.is_wf_Union_support).mono (begin
      rw ← set.Union_union_distrib,
      exact set.Union_subset_Union (λ a, support_add_subset)
    end),
    finite_co_support' := λ g, ((x.finite_co_support g).union (y.finite_co_support g)).subset begin
      intros a ha,
      change (x a).coeff g + (y a).coeff g ≠ 0 at ha,
      rw [set.mem_union, function.mem_support, function.mem_support],
      contrapose! ha,
      rw [ha.1, ha.2, add_zero]
    end }⟩

instance : has_zero (summable_family Γ R α) :=
⟨⟨0, by simp, λ _, by simp⟩⟩

instance : inhabited (summable_family Γ R α) := ⟨0⟩

@[simp]
lemma coe_add {s t : summable_family Γ R α} : ⇑(s + t) = s + t := rfl

lemma add_apply {s t : summable_family Γ R α} {a : α} : (s + t) a = s a + t a := rfl

@[simp]
lemma coe_zero : ((0 : summable_family Γ R α) : α → hahn_series Γ R) = 0 := rfl

lemma zero_apply {a : α} : (0 : summable_family Γ R α) a = 0 := rfl

instance : add_comm_monoid (summable_family Γ R α) :=
{ add := (+),
  zero := 0,
  zero_add := λ s, by { ext, apply zero_add },
  add_zero := λ s, by { ext, apply add_zero },
  add_comm := λ s t, by { ext, apply add_comm },
  add_assoc := λ r s t, by { ext, apply add_assoc } }

/-- The infinite sum of a `summable_family` of Hahn series. -/
def hsum (s : summable_family Γ R α) :
  hahn_series Γ R :=
{ coeff := λ g, ∑ᶠ i, (s i).coeff g,
  is_wf_support' := s.is_wf_Union_support.mono (λ g, begin
    contrapose,
    rw [set.mem_Union, not_exists, function.mem_support, not_not],
    simp_rw [mem_support, not_not],
    intro h,
    rw [finsum_congr h, finsum_zero],
  end) }

@[simp]
lemma hsum_coeff {s : summable_family Γ R α} {g : Γ} :
  s.hsum.coeff g = ∑ᶠ i, (s i).coeff g := rfl

lemma support_hsum_subset {s : summable_family Γ R α} :
  s.hsum.support ⊆ ⋃ (a : α), (s a).support :=
λ g hg, begin
  simp_rw [set.mem_Union, mem_support],
  contrapose! hg,
  rw [mem_support, hsum_coeff, not_not, finsum_congr hg, finsum_zero]
end

@[simp]
lemma hsum_add {s t : summable_family Γ R α} : (s + t).hsum = s.hsum + t.hsum :=
begin
  ext g,
  simp only [add_apply, pi.add_apply, hsum_coeff, ne.def, add_coeff'],
  rw [finsum_add_distrib (s.finite_co_support g) (t.finite_co_support g)],
end

end add_comm_monoid

section add_comm_group
variables [linear_order Γ] [add_comm_group R] {α : Type*} {s t : summable_family Γ R α} {a : α}

instance : add_comm_group (summable_family Γ R α) :=
{ neg := λ s, { to_fun := λ a, - s a,
    is_wf_Union_support' := by { simp_rw [support_neg], exact s.is_wf_Union_support' },
    finite_co_support' := λ g, by { simp only [neg_coeff', pi.neg_apply, ne.def, neg_eq_zero],
      exact s.finite_co_support g } },
  add_left_neg := λ a, by { ext, apply add_left_neg },
  .. summable_family.add_comm_monoid }

@[simp]
lemma coe_neg : ⇑(-s) = - s := rfl

lemma neg_apply : (-s) a = - (s a) := rfl

lemma coe_sub : ⇑(s - t) = s - t := rfl

lemma sub_apply : (s - t) a = s a - t a := rfl

end add_comm_group

section semiring

variables [linear_ordered_add_comm_group Γ] [semiring R] {α : Type*}

instance : has_scalar (hahn_series Γ R) (summable_family Γ R α) :=
{ smul := λ x s, { to_fun := λ a, x * (s a),
    is_wf_Union_support' := begin
      apply (x.is_wf_support.add s.is_wf_Union_support).mono,
      refine set.subset.trans (set.Union_subset_Union (λ a, support_mul_subset_add_support)) _,
      intro g,
      simp only [set.mem_Union, exists_imp_distrib],
      exact λ a ha, (set.add_subset_add (set.subset.refl _) (set.subset_Union _ a)) ha,
    end,
    finite_co_support' := λ g, begin
      have h : (set.add_antidiagonal' g ∩ (x.support.prod (⋃ (a : α), (s a).support))).finite,
      {
          sorry,
      },
      refine (set.finite.bUnion h _).subset _,
      { exact λ ij hij, { a | (s a).coeff ij.snd ≠ 0 } },
      { intros,
        apply s.finite_co_support },
      { intros a ha,
        simp_rw [set.mem_Union],
        contrapose! ha,
        simp only [set.mem_add_antidiagonal', mul_coeff, not_not, ne.def, set.mem_set_of_eq],
        rw [finsum_mem_congr rfl, finsum_mem_zero],
        rintro ⟨i,j⟩ hij,
        by_cases hi : x.coeff i = 0,
        { rw [hi, zero_mul] },
        by_cases hj : (s a).coeff j = 0,
        { rw [hj, mul_zero] },
        rw [not_not.1 (ha ⟨i,j⟩ ⟨hij, hi, set.mem_Union.2 ⟨a, hj⟩⟩), mul_zero] }
    end } }

@[simp]
lemma smul_apply {x : hahn_series Γ R} {s : summable_family Γ R α} {a : α} :
  (x • s) a = x * (s a) := rfl

instance : semimodule (hahn_series Γ R) (summable_family Γ R α) :=
{ smul := (•),
  smul_zero := λ x, ext (λ a, mul_zero _),
  zero_smul := λ x, ext (λ a, zero_mul _),
  one_smul := λ x, ext (λ a, one_mul _),
  add_smul := λ x y s, ext (λ a, add_mul _ _ _),
  smul_add := λ x s t, ext (λ a, mul_add _ _ _),
  mul_smul := λ x y s, ext (λ a, mul_assoc _ _ _) }

@[simp]
lemma hsum_smul {x : hahn_series Γ R} {s : summable_family Γ R α} :
  (x • s).hsum = x * s.hsum :=
begin
  ext g,
  simp only [mul_finsum, set.mem_add_antidiagonal', smul_apply, mul_coeff, hsum_coeff],
  rw [← finsum_mem_univ, finsum_mem_comm', finsum_mem_congr rfl (λ ab hab, _)],
  rw [finsum_mem_univ, mul_finsum (s.finite_co_support ab.snd)],
  sorry,
end

/-- The summation of a `summable_family` as a `linear_map`. -/
@[simps] def lsum : (summable_family Γ R α) →ₗ[hahn_series Γ R] (hahn_series Γ R) :=
⟨hsum, λ _ _, hsum_add, λ _ _, hsum_smul⟩

end semiring

section of_finsupp
variables [linear_order Γ] [add_comm_monoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def of_finsupp (f : α →₀ (hahn_series Γ R)) :
  summable_family Γ R α :=
{ to_fun := f,
  is_wf_Union_support' := begin
      apply (f.support.is_wf_sup (λ a, (f a).support) (λ a ha, (f a).is_wf_support)).mono,
      intros g hg,
      obtain ⟨a, ha⟩ := set.mem_Union.1 hg,
      have haf : a ∈ f.support,
      { rw finsupp.mem_support_iff,
        contrapose! ha,
        rw [ha, support_zero],
        exact set.not_mem_empty _ },
      have h : (λ i, (f i).support) a ≤ _ := le_sup haf,
      exact h ha,
    end,
  finite_co_support' := λ g, f.support.finite_to_set.subset (λ a ha, begin
    rw [mem_coe, finsupp.mem_support_iff],
    contrapose! ha,
    simp [ha]
  end) }

@[simp]
lemma coe_of_finsupp {f : α →₀ (hahn_series Γ R)} : ⇑(summable_family.of_finsupp f) = f := rfl

@[simp]
lemma hsum_of_finsupp {f : α →₀ (hahn_series Γ R)} :
  (of_finsupp f).hsum = f.sum (λ a, id) :=
begin
  ext g,
  simp only [hsum_coeff, coe_of_finsupp],
  simp_rw [← coeff.add_monoid_hom_apply],
  rw [finsupp.sum, add_monoid_hom.map_sum],
  simp_rw [function.id_def],
  refine finsum_eq_sum_of_support_subset _ (λ a ha, _),
  rw [mem_coe, finsupp.mem_support_iff],
  contrapose! ha,
  rw [function.mem_support, not_not, ha, coeff.add_monoid_hom_apply, zero_coeff],
end

end of_finsupp

end summable_family

end hahn_series
