/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.constructions.borel_space

/-!
# Vitali families

On a metric space with a measure `μ`, consider for each `x` a family of closed sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possible non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.

This file defines Vitali families.
-/

open measure_theory metric set filter topological_space
open_locale filter ennreal

variables {α : Type*} [metric_space α]

/-- On a metric space with a measure `μ`, consider for each `x` a family of closed sets with
nonempty interiors, called `sets_at x`. This family is a Vitali family if it satisfies the following
property: consider a (possibly non-measurable) set `s`, and for any `x` in `s` a
subfamily `f x` of `sets_at x` containing sets of arbitrarily small diameter. Then one can extract
a disjoint subfamily covering almost all `s`.

Vitali families are provided by covering theorems such as the Besicovitch covering theorem or the
Vitali covering theorem. They make it possible to formulate general versions of theorems on
differentiations of measure that apply in both contexts.
-/
@[nolint has_inhabited_instance]
structure vitali_family {m : measurable_space α} (μ : measure α) :=
(sets_at : Π (x : α), set (set α))
(center_mem : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → x ∈ y)
(is_closed : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → is_closed y)
(nonempty_interior : ∀ (x : α), ∀ (y : set α), y ∈ sets_at x → (interior y).nonempty)
(nontrivial : ∀ (x : α) (ε > (0 : ℝ)), ∃ y ∈ sets_at x, y ⊆ closed_ball x ε)
(covering : ∀ (s : set α) (f : Π (x : α), set (set α)), (∀ x ∈ s, f x ⊆ sets_at x) →
  (∀ (x ∈ s) (ε > (0 : ℝ)), ∃ a ∈ f x, a ⊆ closed_ball x ε) →
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ pairwise_on t (disjoint on u) ∧ (∀ x ∈ t, u x ∈ f x)
  ∧ μ (s \ ⋃ x ∈ t, u x) = 0)

namespace vitali_family

variables {m : measurable_space α} {μ : measure α}

structure fine_subfamily_on (v : vitali_family μ) (f : α → set (set α)) (s : set α) :=
(subset : ∀ x ∈ s, f x ⊆ v.sets_at x)
(fine : ∀ x ∈ s, ∀ (ε > 0), ∃ a ∈ f x, a ⊆ closed_ball x ε)

namespace fine_subfamily_on

variables {v : vitali_family μ} {f : α → set (set α)} {s : set α} (h : v.fine_subfamily_on f s)
include h

theorem exists_disjoint_covering_ae :
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ pairwise_on t (disjoint on u) ∧ (∀ x ∈ t, u x ∈ f x)
  ∧ μ (s \ ⋃ x ∈ t, u x) = 0 :=
v.covering s f h.subset h.fine

protected def t : set α :=
h.exists_disjoint_covering_ae.some

protected def u : α → set α :=
h.exists_disjoint_covering_ae.some_spec.some

lemma t_subset_s : h.t ⊆ s :=
h.exists_disjoint_covering_ae.some_spec.some_spec.1

lemma u_disjoint : pairwise_on h.t (disjoint on h.u) :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.1

lemma u_mem : ∀ x ∈ h.t, h.u x ∈ f x :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1

lemma measure_diff_bUnion : μ (s \ ⋃ x ∈ h.t, h.u x) = 0 :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.2

lemma t_countable [second_countable_topology α] : countable h.t :=
begin
  apply countable_of_nonempty_interior_of_disjoint h.u (λ x hx, _) h.u_disjoint,
  exact v.nonempty_interior _ _ (h.subset x (h.t_subset_s hx) (h.u_mem x hx)),
end

protected lemma is_closed_u {x : α} (hx : x ∈ h.t) : _root_.is_closed (h.u x) :=
v.is_closed x _ (h.subset x (h.t_subset_s hx) (h.u_mem x hx))

end fine_subfamily_on

variable (v : vitali_family μ)

def filter_at (x : α) : filter (set α) :=
⨅ (ε ∈ Ioi (0 : ℝ)), 𝓟 {a ∈ v.sets_at x | a ⊆ closed_ball x ε}

lemma mem_filter_at_iff {x : α} {s : set (set α)} :
  (s ∈ v.filter_at x) ↔ ∃ (ε > (0 : ℝ)), ∀ a ∈ v.sets_at x, a ⊆ closed_ball x ε → a ∈ s :=
begin
  simp only [filter_at, exists_prop, gt_iff_lt],
  rw mem_binfi_of_directed,
  { simp only [subset_def, and_imp, exists_prop, mem_sep_eq, mem_Ioi, mem_principal] },
  { simp only [directed_on, exists_prop, ge_iff_le, le_principal_iff, mem_Ioi, order.preimage,
      mem_principal],
    assume x hx y hy,
    refine ⟨min x y, lt_min hx hy,
      λ a ha, ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_left _ _))⟩,
      λ a ha, ⟨ha.1, ha.2.trans (closed_ball_subset_closed_ball (min_le_right _ _))⟩⟩ },
  { exact ⟨(1 : ℝ), mem_Ioi.2 zero_lt_one⟩ }
end

lemma eventually_filter_at_iff {x : α} {P : set α → Prop} :
  (∀ᶠ a in v.filter_at x, P a) ↔ ∃ (ε > (0 : ℝ)), ∀ a ∈ v.sets_at x, a ⊆ closed_ball x ε → P a :=
v.mem_filter_at_iff

lemma frequently_filter_at_iff {x : α} {P : set α → Prop} :
  (∃ᶠ a in v.filter_at x, P a) ↔ ∀ (ε > (0 : ℝ)), ∃ a ∈ v.sets_at x, a ⊆ closed_ball x ε ∧ P a :=
by simp only [filter.frequently, eventually_filter_at_iff, not_exists, exists_prop, not_and,
  not_not, not_forall]

theorem ae_eventually_measure_pos [second_countable_topology α] [opens_measurable_space α] :
  ∀ᵐ x ∂μ, ∀ᶠ a in v.filter_at x, 0 < μ a :=
begin
  set s := {x | ¬ (∀ᶠ a in v.filter_at x, 0 < μ a)} with hs,
  simp only [not_lt, not_eventually, nonpos_iff_eq_zero] at hs,
  change μ s = 0,
  let f : α → set (set α) := λ x, {a ∈ v.sets_at x | μ a = 0},
  have h : v.fine_subfamily_on f s,
  { refine ⟨λ x hx y hy, hy.1, λ x hx ε εpos, _⟩,
    rw hs at hx,
    simp only [frequently_filter_at_iff, exists_prop, gt_iff_lt, mem_set_of_eq] at hx,
    rcases hx ε εpos with ⟨a, a_sets, ax, μa⟩,
    exact ⟨a, ⟨a_sets, μa⟩, ax⟩ },
  refine le_antisymm _ bot_le,
  calc μ s ≤ μ ((s \ ⋃ (x ∈ h.t), h.u x) ∪ (⋃ (x ∈ h.t), h.u x)) :
    measure_mono (by simp only [subset_union_left, diff_union_self])
  ... ≤ μ (s \ ⋃ (x ∈ h.t), h.u x) + μ (⋃ (x ∈ h.t), h.u x) : measure_union_le _ _
  ... = 0 + ∑' (x : h.t), μ (h.u x) : by rw [h.measure_diff_bUnion,
    measure_bUnion h.t_countable h.u_disjoint (λ x hx, (h.is_closed_u hx).measurable_set)]
  ... = 0 + ∑' (x : h.t), 0 : by { congr, ext1 x, exact (h.u_mem x x.2).2 }
  ... = 0 : by simp only [tsum_zero, add_zero]
end

theorem eventually_measure_lt_top [is_locally_finite_measure μ] (x : α) :
  ∀ᶠ a in v.filter_at x, μ a < ∞ :=
begin
  obtain ⟨ε, εpos, με⟩ : ∃ (ε : ℝ) (hi : 0 < ε), μ (closed_ball x ε) < ∞ :=
    (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball,
  exact v.eventually_filter_at_iff.2 ⟨ε, εpos, λ a ha haε, (measure_mono haε).trans_lt με⟩,
end

end vitali_family
