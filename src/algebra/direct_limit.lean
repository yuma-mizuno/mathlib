/-
Copyright (c) 2019 Kenny Lau, Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes

Direct limit of modules, abelian groups, rings, and fields.
-/

import linear_algebra.direct_sum_module
import linear_algebra.linear_combination
import linear_algebra.multivariate_polynomial
import ring_theory.ideal_operations
import ring_theory.subring
import data.real.irrational

universes u v w u₁

namespace mv_polynomial

variables {ι : Type u} [decidable_eq ι]

def is_supported (x : mv_polynomial ι ℤ) (s : set ι) : Prop :=
x ∈ ring.closure (X '' s : set (mv_polynomial ι ℤ))

theorem is_supported_upwards {x : mv_polynomial ι ℤ} {s t} (hs : is_supported x s) (hst : s ⊆ t) :
  is_supported x t :=
ring.closure_mono (set.mono_image hst) hs

theorem is_supported_add {x y : mv_polynomial ι ℤ} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x + y) s :=
is_add_submonoid.add_mem hxs hys

theorem is_supported_neg {x : mv_polynomial ι ℤ} {s} (hxs : is_supported x s) :
  is_supported (-x) s :=
is_add_subgroup.neg_mem hxs

theorem is_supported_sub {x y : mv_polynomial ι ℤ} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x - y) s :=
is_add_subgroup.sub_mem _ _ _ hxs hys

theorem is_supported_mul {x y : mv_polynomial ι ℤ} {s} (hxs : is_supported x s) (hys : is_supported y s) :
  is_supported (x * y) s :=
is_submonoid.mul_mem hxs hys

theorem is_supported_zero {s : set ι} : is_supported 0 s :=
is_add_submonoid.zero_mem _

theorem is_supported_one {s : set ι} : is_supported 1 s :=
is_submonoid.one_mem _

theorem is_supported_C {n : ℤ} {s : set ι} : is_supported (C n : mv_polynomial ι ℤ) s :=
int.induction_on n (by rw C_0; exact is_supported_zero)
  (λ n ih, by rw [C_add, C_1]; exact is_supported_add ih is_supported_one)
  (λ n ih, by rw [C_sub, C_1]; exact is_supported_sub ih is_supported_one)

def restriction (s : set ι) [decidable_pred s] (x : mv_polynomial ι ℤ) : mv_polynomial s ℤ :=
eval₂ C (λ p, if H : p ∈ s then X (⟨p, H⟩ : s) else 0) x

section restriction
variables (s : set ι) [decidable_pred s] (x y : mv_polynomial ι ℤ)
@[simp] lemma restriction_X (p) : restriction s (X p : mv_polynomial ι ℤ) = if H : p ∈ s then X ⟨p, H⟩ else 0 := eval₂_X _ _ _
@[simp] lemma restriction_zero : restriction s (0 : mv_polynomial ι ℤ) = 0 := eval₂_zero _ _
@[simp] lemma restriction_one : restriction s (1 : mv_polynomial ι ℤ) = 1 := eval₂_one _ _
@[simp] lemma restriction_add : restriction s (x + y) = restriction s x + restriction s y := eval₂_add _ _
@[simp] lemma restriction_neg : restriction s (-x) = -restriction s x := eval₂_neg _ _ _
@[simp] lemma restriction_sub : restriction s (x - y) = restriction s x - restriction s y := eval₂_sub _ _ _
@[simp] lemma restriction_mul : restriction s (x * y) = restriction s x * restriction s y := eval₂_mul _ _
end restriction

theorem is_supported_X {p} {s : set ι} : is_supported (X p : mv_polynomial ι ℤ) s ↔ p ∈ s :=
suffices is_supported (X p) s → p ∈ s, from ⟨this, λ hps, ring.subset_closure ⟨p, hps, rfl⟩⟩,
assume hps : is_supported (X p) s, begin
  haveI : decidable_pred s := classical.dec_pred s,
  haveI : is_ring_hom (coe : ℤ → ℝ) := int.cast.is_ring_hom,
  have : ∀ x : mv_polynomial ι ℤ, is_supported x s → ∃ q : ℚ, eval₂ (coe : ℤ → ℝ) (λ q, if q ∈ s then 0 else real.sqrt 2) x = ↑q,
  { intros x hx, refine ring.in_closure.rec_on hx _ _ _ _,
    { use 1, rw [eval₂_one, rat.cast_one] },
    { use -1, rw [eval₂_neg, eval₂_one, rat.cast_neg, rat.cast_one], },
    { rintros _ ⟨z, hzs, rfl⟩ _ _, use 0, rw [eval₂_mul, eval₂_X, if_pos hzs, zero_mul, rat.cast_zero] },
    { rintros x y ⟨q, hq⟩ ⟨r, hr⟩, use q+r, rw [eval₂_add, hq, hr, rat.cast_add] } },
  specialize this (X p) hps, rw [eval₂_X] at this, split_ifs at this, { exact h },
  exfalso, exact irr_sqrt_two this
end

theorem exists_finite_support (x : mv_polynomial ι ℤ) : ∃ s : set ι, set.finite s ∧ is_supported x s :=
induction_on x
  (λ n, ⟨∅, set.finite_empty, is_supported_C⟩)
  (λ x y ⟨s, hfs, hxs⟩ ⟨t, hft, hxt⟩, ⟨s ∪ t, set.finite_union hfs hft, is_supported_add
    (is_supported_upwards hxs $ set.subset_union_left s t)
    (is_supported_upwards hxt $ set.subset_union_right s t)⟩)
  (λ x n ⟨s, hfs, hxs⟩, ⟨insert n s, set.finite_insert n hfs, is_supported_mul
    (is_supported_upwards hxs $ set.subset_insert n s)
    (is_supported_X.2 $ set.mem_insert n s)⟩)

theorem exists_finset_support (x : mv_polynomial ι ℤ) : ∃ s : finset ι, is_supported x ↑s :=
let ⟨s, hfs, hxs⟩ := exists_finite_support x in ⟨hfs.to_finset, by rwa finset.coe_to_finset⟩

end mv_polynomial

open lattice submodule

variables {R : Type u} [ring R]
variables {ι : Type v} [nonempty ι]
variables [directed_order ι] [decidable_eq ι]
variables (G : ι → Type w) [Π i, decidable_eq (G i)]

class directed_system (f : Π i j, i ≤ j → G i → G j) : Prop :=
(map_self : ∀ i x h, f i i h x = x)
(map_map : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

namespace module

variables [Π i, add_comm_group (G i)] [Π i, module R (G i)]

class directed_system (f : Π i j, i ≤ j → G i →ₗ[R] G j) : Prop :=
(map_self : ∀ i x h, f i i h x = x)
(map_map : ∀ i j k hij hjk x, f j k hjk (f i j hij x) = f i k (le_trans hij hjk) x)

variables (f : Π i j, i ≤ j → G i →ₗ[R] G j) [directed_system G f]

def direct_limit : Type (max v w) :=
(span R $ { a | ∃ (i j) (H : i ≤ j) x,
  direct_sum.lof R ι G i x - direct_sum.lof R ι G j (f i j H x) = a }).quotient

namespace direct_limit

instance : add_comm_group (direct_limit G f) := quotient.add_comm_group _
instance : module R (direct_limit G f) := quotient.module _

variables (R ι)
def of (i) : G i →ₗ[R] direct_limit G f :=
(mkq _).comp $ direct_sum.lof R ι G i
variables {R ι G f}

@[simp] lemma of_f {i j hij x} : (of R ι G f j (f i j hij x)) = of R ι G f i x :=
eq.symm $ (submodule.quotient.eq _).2 $ subset_span ⟨i, j, hij, x, rfl⟩

theorem exists_of (z : direct_limit G f) : ∃ i x, of R ι G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ z, direct_sum.induction_on z
  ⟨ind, 0, linear_map.map_zero _⟩
  (λ i x, ⟨i, x, rfl⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [linear_map.map_add, of_f, of_f, ihx, ihy]; refl⟩)

@[elab_as_eliminator]
protected theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of R ι G f i x)) : C z :=
let ⟨i, x, h⟩ := exists_of z in h ▸ ih i x

variables {P : Type u₁} [add_comm_group P] [module R P] (g : Π i, G i →ₗ[R] P)
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

variables (R ι G f)
def lift : direct_limit G f →ₗ[R] P :=
liftq _ (direct_sum.to_module R ι P g)
  (span_le.2 $ λ a ⟨i, j, hij, x, hx⟩, by rw [← hx, mem_coe, linear_map.sub_mem_ker_iff,
    direct_sum.to_module_lof, direct_sum.to_module_lof, Hg])
variables {R ι G f}

omit Hg
lemma lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x :=
direct_sum.to_module_lof R _ _

theorem lift_unique (F : direct_limit G f →ₗ[R] P) (x) :
  F x = lift R ι G f (λ i, F.comp $ of R ι G f i)
    (λ i j hij x, by rw [linear_map.comp_apply, of_f]; refl) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of; refl

section totalize
local attribute [instance, priority 0] classical.dec
variables (G f)
noncomputable def totalize : Π i j, G i →ₗ[R] G j :=
λ i j, if h : i ≤ j then f i j h else 0
variables {G f}

lemma totalize_apply (i j x) :
  totalize G f i j x = if h : i ≤ j then f i j h x else 0 :=
if h : i ≤ j
  then by dsimp only [totalize]; rw [dif_pos h, dif_pos h]
  else by dsimp only [totalize]; rw [dif_neg h, dif_neg h, linear_map.zero_apply]
end totalize

lemma to_module_totalize_of_le {x : direct_sum ι G} {i j : ι}
  (hij : i ≤ j) (hx : ∀ k ∈ x.support, k ≤ i) :
  direct_sum.to_module R ι (G j) (λ k, totalize G f k j) x =
  f i j hij (direct_sum.to_module R ι (G i) (λ k, totalize G f k i) x) :=
begin
  rw [← @dfinsupp.sum_single ι G _ _ _ x, dfinsupp.sum],
  simp only [linear_map.map_sum],
  refine finset.sum_congr rfl (λ k hk, _),
  rw direct_sum.single_eq_lof R k (x k),
  simp [totalize_apply, hx k hk, le_trans (hx k hk) hij, directed_system.map_map f]
end

lemma of.zero_exact_aux {x : direct_sum ι G} (H : submodule.quotient.mk x = (0 : direct_limit G f)) :
  ∃ j, (∀ k ∈ x.support, k ≤ j) ∧ direct_sum.to_module R ι (G j) (λ i, totalize G f i j) x = (0 : G j) :=
nonempty.elim (by apply_instance) $ assume ind : ι,
span_induction ((quotient.mk_eq_zero _).1 H)
  (λ x ⟨i, j, hij, y, hxy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, begin
      clear_,
      subst hxy,
      split,
      { intros i0 hi0,
        rw [dfinsupp.mem_support_iff, dfinsupp.sub_apply, ← direct_sum.single_eq_lof,
            ← direct_sum.single_eq_lof, dfinsupp.single_apply, dfinsupp.single_apply] at hi0,
        split_ifs at hi0 with hi hj hj, { rwa hi at hik }, { rwa hi at hik }, { rwa hj at hjk },
        exfalso, apply hi0, rw sub_zero },
      simp [linear_map.map_sub, totalize_apply, hik, hjk,
        directed_system.map_map f, direct_sum.apply_eq_component,
        direct_sum.component.of],
    end⟩)
  ⟨ind, λ _ h, (finset.not_mem_empty _ h).elim, linear_map.map_zero _⟩
  (λ x y ⟨i, hi, hxi⟩ ⟨j, hj, hyj⟩,
    let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, λ l hl,
      (finset.mem_union.1 (dfinsupp.support_add hl)).elim
        (λ hl, le_trans (hi _ hl) hik)
        (λ hl, le_trans (hj _ hl) hjk),
      by simp [linear_map.map_add, hxi, hyj,
          to_module_totalize_of_le hik hi,
          to_module_totalize_of_le hjk hj]⟩)
  (λ a x ⟨i, hi, hxi⟩,
    ⟨i, λ k hk, hi k (dfinsupp.support_smul hk),
      by simp [linear_map.map_smul, hxi]⟩)

theorem of.zero_exact {i x} (H : of R ι G f i x = 0) :
  ∃ j hij, f i j hij x = (0 : G j) :=
let ⟨j, hj, hxj⟩ := of.zero_exact_aux H in
if hx0 : x = 0 then ⟨i, le_refl _, by simp [hx0]⟩
else
  have hij : i ≤ j, from hj _ $
    by simp [direct_sum.apply_eq_component, hx0],
  ⟨j, hij, by simpa [totalize_apply, hij] using hxj⟩

end direct_limit

end module


namespace add_comm_group

variables [Π i, add_comm_group (G i)]

def direct_limit (f : Π i j, i ≤ j → G i → G j)
  [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f] : Type* :=
@module.direct_limit ℤ _ ι _ _ _ G _ _ _
  (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)
  ⟨directed_system.map_self f, directed_system.map_map f⟩

namespace direct_limit

variables (f : Π i j, i ≤ j → G i → G j)
variables [Π i j hij, is_add_group_hom (f i j hij)] [directed_system G f]

def directed_system : module.directed_system G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij) :=
⟨directed_system.map_self f, directed_system.map_map f⟩

local attribute [instance] directed_system

instance : add_comm_group (direct_limit G f) :=
module.direct_limit.add_comm_group G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)

set_option class.instance_max_depth 50

def of (i) : G i → direct_limit G f :=
module.direct_limit.of ℤ ι G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij) i
variables {G f}

instance of.is_add_group_hom (i) : is_add_group_hom (of G f i) :=
linear_map.is_add_group_hom _

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
module.direct_limit.of_f

@[simp] lemma of_zero (i) : of G f i 0 = 0 := is_add_group_hom.zero _
@[simp] lemma of_add (i x y) : of G f i (x + y) = of G f i x + of G f i y := is_add_group_hom.add _ _ _
@[simp] lemma of_neg (i x) : of G f i (-x) = -of G f i x := is_add_group_hom.neg _ _
@[simp] lemma of_sub (i x y) : of G f i (x - y) = of G f i x - of G f i y := is_add_group_hom.sub _ _ _

@[elab_as_eliminator]
protected theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
module.direct_limit.induction_on z ih

theorem of.zero_exact (i x) (h : of G f i x = 0) : ∃ j hij, f i j hij x = 0 :=
module.direct_limit.of.zero_exact h

variables (P : Type u₁) [add_comm_group P]
variables (g : Π i, G i → P) [Π i, is_add_group_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

variables (G f)
def lift : direct_limit G f → P :=
module.direct_limit.lift ℤ ι G (λ i j hij, is_add_group_hom.to_linear_map $ f i j hij)
  (λ i, is_add_group_hom.to_linear_map $ g i) Hg
variables {G f}

instance lift.is_add_group_hom : is_add_group_hom (lift G f P g Hg) :=
linear_map.is_add_group_hom _

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x :=
module.direct_limit.lift_of _ _ _

@[simp] lemma lift_zero : lift G f P g Hg 0 = 0 := is_add_group_hom.zero _
@[simp] lemma lift_add (x y) : lift G f P g Hg (x + y) = lift G f P g Hg x + lift G f P g Hg y := is_add_group_hom.add _ _ _
@[simp] lemma lift_neg (x) : lift G f P g Hg (-x) = -lift G f P g Hg x := is_add_group_hom.neg _ _
@[simp] lemma lift_sub (x y) : lift G f P g Hg (x - y) = lift G f P g Hg x - lift G f P g Hg y := is_add_group_hom.sub _ _ _

lemma lift_unique (F : direct_limit G f → P) [is_add_group_hom F] (x) :
  F x = lift G f P (λ i x, F $ of G f i x) (λ i j hij x, by rw of_f) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of

end direct_limit

end add_comm_group


namespace ring

variables [Π i, comm_ring (G i)]
variables (f : Π i j, i ≤ j → G i → G j)
variables [Π i j hij, is_ring_hom (f i j hij)]
variables [directed_system G f]

open mv_polynomial

def direct_limit : Type (max v w) :=
(ideal.span { a : mv_polynomial (Σ i, G i) ℤ | (∃ i j H x, X (⟨j, f i j H x⟩ : Σ i, G i) - X ⟨i, x⟩ = a) ∨
  (∃ i, X (⟨i, 1⟩ : Σ i, G i) - 1 = a) ∨
  (∃ i x y, X (⟨i, x + y⟩ : Σ i, G i) - (X ⟨i, x⟩ + X ⟨i, y⟩) = a) ∨
  (∃ i x y, X (⟨i, x * y⟩ : Σ i, G i) - (X ⟨i, x⟩ * X ⟨i, y⟩) = a) }).quotient

namespace direct_limit

instance : comm_ring (direct_limit G f) :=
ideal.quotient.comm_ring _

instance : ring (direct_limit G f) :=
comm_ring.to_ring _

def of (i) (x : G i) : direct_limit G f :=
ideal.quotient.mk _ $ X ⟨i, x⟩

variables {G f}

instance of.is_ring_hom (i) : is_ring_hom (of G f i) :=
{ map_one := ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inl ⟨i, rfl⟩,
  map_mul := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inr ⟨i, x, y, rfl⟩,
  map_add := λ x y, ideal.quotient.eq.2 $ subset_span $ or.inr $ or.inr $ or.inl ⟨i, x, y, rfl⟩ }

@[simp] lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x :=
ideal.quotient.eq.2 $ subset_span $ or.inl ⟨i, j, hij, x, rfl⟩

@[simp] lemma of_zero (i) : of G f i 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma of_one (i) : of G f i 1 = 1 := is_ring_hom.map_one _
@[simp] lemma of_add (i x y) : of G f i (x + y) = of G f i x + of G f i y := is_ring_hom.map_add _
@[simp] lemma of_neg (i x) : of G f i (-x) = -of G f i x := is_ring_hom.map_neg _
@[simp] lemma of_sub (i x y) : of G f i (x - y) = of G f i x - of G f i y := is_ring_hom.map_sub _
@[simp] lemma of_mul (i x y) : of G f i (x * y) = of G f i x * of G f i y := is_ring_hom.map_mul _
@[simp] lemma of_pow (i x) (n : ℕ) : of G f i (x ^ n) = of G f i x ^ n := is_semiring_hom.map_pow _ _ _

theorem exists_of (z : direct_limit G f) : ∃ i x, of G f i x = z :=
nonempty.elim (by apply_instance) $ assume ind : ι,
quotient.induction_on' z $ λ x, induction_on x
  (λ n, ⟨ind, n, int.induction_on n (by rw [int.cast_zero, of_zero, C_0]; refl)
    (λ n ih, by rw [int.cast_add, int.cast_one, of_add, ih, of_one, C_add, C_1]; refl)
    (λ n ih, by rw [int.cast_sub, int.cast_one, of_sub, ih, of_one, C_sub, C_1]; refl)⟩)
  (λ p q ⟨i, x, ihx⟩ ⟨j, y, ihy⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x + f j k hjk y, by rw [of_add, of_f, of_f, ihx, ihy]; refl⟩)
  (λ p ⟨j, y⟩ ⟨i, x, ihx⟩, let ⟨k, hik, hjk⟩ := directed_order.directed i j in
    ⟨k, f i k hik x * f j k hjk y, by rw [of_mul, of_f, of_f, ihx]; refl⟩)

@[elab_as_eliminator] theorem induction_on {C : direct_limit G f → Prop} (z : direct_limit G f)
  (ih : ∀ i x, C (of G f i x)) : C z :=
let ⟨i, x, hx⟩ := exists_of z in hx ▸ ih i x

section of_zero_exact_aux
attribute [instance, priority 0] classical.dec
variables (G f)
lemma of.zero_exact_aux2 {x : mv_polynomial (Σ i, G i) ℤ} {s t} (hxs : is_supported x s) {j k}
  (hj : ∀ z : Σ i, G i, z ∈ s → z.1 ≤ j) (hk : ∀ z : Σ i, G i, z ∈ t → z.1 ≤ k)
  (hjk : j ≤ k) (hst : s ⊆ t) :
  f j k hjk (eval₂ coe (λ ix : s, f ix.1.1 j (hj ix ix.2) ix.1.2) (restriction s x)) =
  eval₂ coe (λ ix : t, f ix.1.1 k (hk ix ix.2) ix.1.2) (restriction t x) :=
begin
  haveI : is_ring_hom (coe : ℤ → G j) := int.cast.is_ring_hom,
  haveI : is_ring_hom (coe : ℤ → G k) := int.cast.is_ring_hom,
  refine ring.in_closure.rec_on hxs _ _ _ _,
  { rw [restriction_one, eval₂_one, is_ring_hom.map_one (f j k hjk), restriction_one, eval₂_one] },
  { rw [restriction_neg, restriction_one, eval₂_neg, eval₂_one,
      is_ring_hom.map_neg (f j k hjk), is_ring_hom.map_one (f j k hjk),
      restriction_neg, restriction_one, eval₂_neg, eval₂_one] },
  { rintros _ ⟨p, hps, rfl⟩ n ih,
    rw [restriction_mul, eval₂_mul, is_ring_hom.map_mul (f j k hjk), ih, restriction_mul, eval₂_mul,
        restriction_X, dif_pos hps, eval₂_X, restriction_X, dif_pos (hst hps), eval₂_X],
    dsimp only, rw directed_system.map_map f, refl },
  { rintros x y ihx ihy,
    rw [restriction_add, eval₂_add, is_ring_hom.map_add (f j k hjk), ihx, ihy, restriction_add, eval₂_add] }
end
variables {G f}

lemma of.zero_exact_aux {x : mv_polynomial (Σ i, G i) ℤ} (H : ideal.quotient.mk _ x = (0 : direct_limit G f)) :
  ∃ j s, ∃ H : (∀ k : Σ i, G i, k ∈ s → k.1 ≤ j), is_supported x s ∧
    eval₂ coe (λ ix : s, f ix.1.1 j (H ix ix.2) ix.1.2) (restriction s x) = (0 : G j) :=
begin
  refine span_induction (ideal.quotient.eq_zero_iff_mem.1 H) _ _ _ _,
  { rintros x (⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩),
    { refine ⟨j, {⟨i, x⟩, ⟨j, f i j hij x⟩}, _,
        is_supported_sub (is_supported_X.2 $ or.inl rfl) (is_supported_X.2 $ or.inr $ or.inl rfl), _⟩,
      { rintros k (rfl | ⟨rfl | h⟩), refl, exact hij, cases h },
      { haveI : is_ring_hom (coe : ℤ → G j) := int.cast.is_ring_hom,
        rw [restriction_sub, eval₂_sub, restriction_X, dif_pos, restriction_X, dif_pos, eval₂_X, eval₂_X],
        dsimp only, rw directed_system.map_map f, exact sub_self _,
        { left, refl }, { right, left, refl }, } },
    { refine ⟨i, {⟨i, 1⟩}, _, is_supported_sub (is_supported_X.2 $ or.inl rfl) is_supported_one, _⟩,
      { rintros k (rfl | h), refl, cases h },
      { haveI : is_ring_hom (coe : ℤ → G i) := int.cast.is_ring_hom,
        rw [restriction_sub, eval₂_sub, restriction_X, dif_pos, restriction_one, eval₂_X, eval₂_one],
        dsimp only, rw [is_ring_hom.map_one (f i i _), sub_self], exact _inst_7 i i _, { left, refl } } },
    { refine ⟨i, {⟨i, x+y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_X.2 $ or.inr $ or.inr $ or.inl rfl)
          (is_supported_add (is_supported_X.2 $ or.inr $ or.inl rfl) (is_supported_X.2 $ or.inl rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩), refl, refl, refl, cases hk },
      { haveI : is_ring_hom (coe : ℤ → G i) := int.cast.is_ring_hom,
        rw [restriction_sub, restriction_add, restriction_X, restriction_X, restriction_X,
          dif_pos, dif_pos, dif_pos, eval₂_sub, eval₂_add, eval₂_X, eval₂_X, eval₂_X],
        dsimp only, rw is_ring_hom.map_add (f i i _), exact sub_self _,
        { right, right, left, refl }, { apply_instance }, { left, refl }, { right, left, refl } } },
    { refine ⟨i, {⟨i, x*y⟩, ⟨i, x⟩, ⟨i, y⟩}, _,
        is_supported_sub (is_supported_X.2 $ or.inr $ or.inr $ or.inl rfl)
          (is_supported_mul (is_supported_X.2 $ or.inr $ or.inl rfl) (is_supported_X.2 $ or.inl rfl)), _⟩,
      { rintros k (rfl | ⟨rfl | ⟨rfl | hk⟩⟩), refl, refl, refl, cases hk },
      { haveI : is_ring_hom (coe : ℤ → G i) := int.cast.is_ring_hom,
        rw [restriction_sub, restriction_mul, restriction_X, restriction_X, restriction_X,
          dif_pos, dif_pos, dif_pos, eval₂_sub, eval₂_mul, eval₂_X, eval₂_X, eval₂_X],
        dsimp only, rw is_ring_hom.map_mul (f i i _), exact sub_self _,
        { right, right, left, refl }, { apply_instance }, { left, refl }, { right, left, refl } } } },
  { refine nonempty.elim (by apply_instance) (assume ind : ι, _),
    refine ⟨ind, ∅, λ _, false.elim, is_supported_zero, _⟩,
    rw [restriction_zero, eval₂_zero] },
  { rintros x y ⟨i, s, hi, hxs, ihs⟩ ⟨j, t, hj, hyt, iht⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz), exact le_trans (hi z hz) hik, exact le_trans (hj z hz) hjk },
    refine ⟨k, s ∪ t, this, is_supported_add (is_supported_upwards hxs $ set.subset_union_left s t)
      (is_supported_upwards hyt $ set.subset_union_right s t), _⟩,
    { haveI : is_ring_hom (coe : ℤ → G k) := int.cast.is_ring_hom,
      rw [restriction_add, eval₂_add,
        ← of.zero_exact_aux2 G f hxs hi this hik (set.subset_union_left s t),
        ← of.zero_exact_aux2 G f hyt hj this hjk (set.subset_union_right s t),
        ihs, is_ring_hom.map_zero (f i k hik), iht, is_ring_hom.map_zero (f j k hjk), zero_add] } },
  { rintros x y ⟨j, t, hj, hyt, iht⟩, rw smul_eq_mul,
    rcases exists_finset_support x with ⟨s, hxs⟩,
    rcases (s.image sigma.fst).exists_le with ⟨i, hi⟩,
    rcases directed_order.directed i j with ⟨k, hik, hjk⟩,
    have : ∀ z : Σ i, G i, z ∈ ↑s ∪ t → z.1 ≤ k,
    { rintros z (hz | hz), exact le_trans (hi z.1 $ finset.mem_image.2 ⟨z, hz, rfl⟩) hik, exact le_trans (hj z hz) hjk },
    refine ⟨k, ↑s ∪ t, this, is_supported_mul (is_supported_upwards hxs $ set.subset_union_left ↑s t)
      (is_supported_upwards hyt $ set.subset_union_right ↑s t), _⟩,
    haveI : is_ring_hom (coe : ℤ → G k) := int.cast.is_ring_hom,
    rw [restriction_mul, eval₂_mul,
        ← of.zero_exact_aux2 G f hyt hj this hjk (set.subset_union_right ↑s t),
        iht, is_ring_hom.map_zero (f j k hjk), mul_zero] }
end
end of_zero_exact_aux

lemma of.zero_exact {i x} (hix : of G f i x = 0) : ∃ j, ∃ hij : i ≤ j, f i j hij x = 0 :=
let ⟨j, s, H, hxs, hx⟩ := of.zero_exact_aux hix in
have hixs : (⟨i, x⟩ : Σ i, G i) ∈ s, from is_supported_X.1 hxs,
⟨j, H ⟨i, x⟩ hixs, by haveI : is_ring_hom (coe : ℤ → G j) := int.cast.is_ring_hom;
rw [restriction_X, dif_pos hixs, eval₂_X] at hx; exact hx⟩

theorem of_inj (hf : ∀ i j hij, function.injective (f i j hij)) (i) :
  function.injective (of G f i) :=
begin
  suffices : ∀ x, of G f i x = 0 → x = 0,
  { intros x y hxy, rw ← sub_eq_zero_iff_eq, apply this,
    rw [is_ring_hom.map_sub (of G f i), hxy, sub_self] },
  intros x hx, rcases of.zero_exact hx with ⟨j, hij, hfx⟩,
  apply hf i j hij, rw [hfx, is_ring_hom.map_zero (f i j hij)]
end

variables (P : Type u₁) [comm_ring P]
variables (g : Π i, G i → P) [Π i, is_ring_hom (g i)]
variables (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)
include Hg

set_option profiler true
variables (G f)
def lift : direct_limit G f → P :=
by haveI : is_ring_hom (coe : ℤ → P) := int.cast.is_ring_hom; exact
ideal.quotient.lift _ (eval₂ coe $ λ x : Σ i, G i, g x.1 x.2) begin
  haveI : is_ring_hom (eval₂ (coe : ℤ → P) $ λ x : Σ i, G i, g x.1 x.2) := eval₂.is_ring_hom _ _,
  suffices : ideal.span _ ≤ ideal.comap (eval₂ (coe : ℤ → P) $ λ x : Σ i, G i, g x.1 x.2) ⊥,
  { intros x hx, exact (mem_bot P).1 (this hx) },
  rw ideal.span_le, intros x hx,
  rw [mem_coe, ideal.mem_comap, mem_bot],
  rcases hx with ⟨i, j, hij, x, rfl⟩ | ⟨i, rfl⟩ | ⟨i, x, y, rfl⟩ | ⟨i, x, y, rfl⟩;
  simp only [eval₂_sub, eval₂_X, Hg, eval₂_one, eval₂_add, eval₂_mul,
      is_ring_hom.map_one (g i), is_ring_hom.map_add (g i), is_ring_hom.map_mul (g i), sub_self]
end
set_option profiler false
variables {G f}
omit Hg
#print lift
instance lift.is_ring_hom : is_ring_hom (lift G f P g Hg) :=
⟨free_comm_ring.lift_one _,
λ x y, quotient.induction_on₂' x y $ λ p q, free_comm_ring.lift_mul _ _ _,
λ x y, quotient.induction_on₂' x y $ λ p q, free_comm_ring.lift_add _ _ _⟩

@[simp] lemma lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := free_comm_ring.lift_of _ _
@[simp] lemma lift_zero : lift G f P g Hg 0 = 0 := is_ring_hom.map_zero _
@[simp] lemma lift_one : lift G f P g Hg 1 = 1 := is_ring_hom.map_one _
@[simp] lemma lift_add (x y) : lift G f P g Hg (x + y) = lift G f P g Hg x + lift G f P g Hg y := is_ring_hom.map_add _
@[simp] lemma lift_neg (x) : lift G f P g Hg (-x) = -lift G f P g Hg x := is_ring_hom.map_neg _
@[simp] lemma lift_sub (x y) : lift G f P g Hg (x - y) = lift G f P g Hg x - lift G f P g Hg y := is_ring_hom.map_sub _
@[simp] lemma lift_mul (x y) : lift G f P g Hg (x * y) = lift G f P g Hg x * lift G f P g Hg y := is_ring_hom.map_mul _
@[simp] lemma lift_pow (x) (n : ℕ) : lift G f P g Hg (x ^ n) = lift G f P g Hg x ^ n := is_semiring_hom.map_pow _ _ _

theorem lift_unique (F : direct_limit G f → P) [is_ring_hom F] (x) :
  F x = lift G f P (λ i x, F $ of G f i x) (λ i j hij x, by rw [of_f]) x :=
direct_limit.induction_on x $ λ i x, by rw lift_of

end direct_limit

end ring


namespace field

variables [Π i, field (G i)]
variables (f : Π i j, i ≤ j → G i → G j) [Π i j hij, is_field_hom (f i j hij)]
variables [directed_system G f]

namespace direct_limit

instance nonzero_comm_ring : nonzero_comm_ring (ring.direct_limit G f) :=
{ zero_ne_one := nonempty.elim (by apply_instance) $ assume i : ι, begin
    change (0 : ring.direct_limit G f) ≠ 1,
    rw ← ring.direct_limit.of_one,
    intros H, rcases ring.direct_limit.of.zero_exact H.symm with ⟨j, hij, hf⟩,
    rw is_ring_hom.map_one (f i j hij) at hf,
    exact one_ne_zero hf
  end,
  .. ring.direct_limit.comm_ring G f }

theorem exists_inv {p : ring.direct_limit G f} : p ≠ 0 → ∃ y, p * y = 1 :=
ring.direct_limit.induction_on p $ λ i x H,
⟨ring.direct_limit.of G f i (x⁻¹), by erw [← ring.direct_limit.of_mul,
    mul_inv_cancel (assume h : x = 0, H $ by rw [h, ring.direct_limit.of_zero]),
    ring.direct_limit.of_one]⟩

section
local attribute [instance, priority 0] classical.dec

noncomputable def inv (p : ring.direct_limit G f) : ring.direct_limit G f :=
if H : p = 0 then 0 else classical.some (direct_limit.exists_inv G f H)

protected theorem mul_inv_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : p * inv G f p = 1 :=
by rw [inv, dif_neg hp, classical.some_spec (direct_limit.exists_inv G f hp)]

protected theorem inv_mul_cancel {p : ring.direct_limit G f} (hp : p ≠ 0) : inv G f p * p = 1 :=
by rw [_root_.mul_comm, direct_limit.mul_inv_cancel G f hp]

protected noncomputable def field : field (ring.direct_limit G f) :=
{ inv := inv G f,
  mul_inv_cancel := λ p, direct_limit.mul_inv_cancel G f,
  inv_mul_cancel := λ p, direct_limit.inv_mul_cancel G f,
  .. direct_limit.nonzero_comm_ring G f }
end

end direct_limit

end field
