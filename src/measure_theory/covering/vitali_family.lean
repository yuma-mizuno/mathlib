/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.measure.regular
import measure_theory.function.ae_measurable_order
import measure_theory.integral.lebesgue
import measure_theory.decomposition.radon_nikodym

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

This file defines Vitali families and proves the main differentiation theorem for measures along
Vitali families: for almost every `x`, the ratio `ρ a / μ a` tends (when `a` shrinks to `x` along
the Vitali family) towards the Radon-Nikodym derivative of `ρ` with respect to `μ` at `x`.

## Main definitions

* `vitali_family μ` is a structure made, for each `x : X`, of a family of sets around `x`, such that
one can extract an almost everywhere disjoint covering from any subfamily containing sets of
arbitrarily small diameters.

Let `v` be such a Vitali family.
* `v.filter_at x` is a filter on sets of `X`, such that convergence with respect to this filter
means convergence when sets in the Vitali family shrink towards `x`.

-/

open measure_theory metric set filter topological_space measure_theory.measure
open_locale filter ennreal measure_theory nnreal topological_space

local attribute [instance] emetric.second_countable_of_sigma_compact

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

variables {m0 : measurable_space α} {μ : measure α}
include μ

/-- A Vitali family for a measure `μ` is also a Vitali family for any measure absolutely continuous
with respect to `μ`. -/
def mono (v : vitali_family μ) (ν : measure α) (hν : ν ≪ μ) :
  vitali_family ν :=
{ sets_at := v.sets_at,
  center_mem := v.center_mem,
  is_closed := v.is_closed,
  nonempty_interior := v.nonempty_interior,
  nontrivial := v.nontrivial,
  covering := λ s f h h', begin
    rcases v.covering s f h h' with ⟨t, u, ts, u_disj, uf, μu⟩,
    exact ⟨t, u, ts, u_disj, uf, hν μu⟩
  end }

/-- Given a Vitali family `v` for a measure `μ`, a family `f` is a fine subfamily on a set `s` if
every point `x` in `s` belongs to arbitrarily small sets in `v.sets_at x ∩ f x`. This is precisely
the subfamilies for which the Vitali family definition ensures that one can extract a disjoint
covering of almost all `s`. -/
def fine_subfamily_on (v : vitali_family μ) (f : α → set (set α)) (s : set α) : Prop :=
∀ x ∈ s, ∀ (ε > 0), ∃ a ∈ v.sets_at x ∩ f x, a ⊆ closed_ball x ε

namespace fine_subfamily_on

variables {v : vitali_family μ} {f : α → set (set α)} {s : set α} (h : v.fine_subfamily_on f s)
include h

theorem exists_disjoint_covering_ae :
  ∃ (t : set α) (u : α → set α), t ⊆ s ∧ pairwise_on t (disjoint on u) ∧
    (∀ x ∈ t, u x ∈ v.sets_at x ∩ f x) ∧ μ (s \ ⋃ x ∈ t, u x) = 0 :=
v.covering s (λ x, v.sets_at x ∩ f x) (λ x hx, inter_subset_left _ _) h

/-- Given `h : v.fine_subfamily_on f s`, then `h.t` is a subset of `s` parametrizing a disjoint
covering of almost every `s`. -/
protected def t : set α :=
h.exists_disjoint_covering_ae.some

/-- Given `h : v.fine_subfamily_on f s`, then `h.u x` is a set in the family, for `x ∈ h.t`, such
that these sets form a disjoint covering of almost every `s`. -/
protected def u : α → set α :=
h.exists_disjoint_covering_ae.some_spec.some

lemma t_subset_s : h.t ⊆ s :=
h.exists_disjoint_covering_ae.some_spec.some_spec.1

lemma u_disjoint : pairwise_on h.t (disjoint on h.u) :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.1

lemma u_disjoint_subtype : pairwise (disjoint on (λ x : h.t, h.u x)) :=
(pairwise_subtype_iff_pairwise_on _ _).2 h.u_disjoint

lemma u_mem_f {x : α} (hx : x ∈ h.t) : h.u x ∈ f x :=
(h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).2

lemma u_mem_v {x : α} (hx : x ∈ h.t) : h.u x ∈ v.sets_at x :=
(h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.1 x hx).1

lemma measure_diff_bUnion : μ (s \ ⋃ x ∈ h.t, h.u x) = 0 :=
h.exists_disjoint_covering_ae.some_spec.some_spec.2.2.2

lemma t_countable [second_countable_topology α] : countable h.t :=
countable_of_nonempty_interior_of_disjoint h.u (λ x hx, v.nonempty_interior _ _ (h.u_mem_v hx))
  h.u_disjoint

protected lemma is_closed_u {x : α} (hx : x ∈ h.t) : _root_.is_closed (h.u x) :=
v.is_closed x _ (h.u_mem_v hx)

lemma measure_le_tsum_of_absolutely_continuous
  [second_countable_topology α] [opens_measurable_space α]
  {ρ : measure α} (hρ : ρ ≪ μ) :
  ρ s ≤ ∑' (x : h.t), ρ (h.u x) :=
calc ρ s ≤ ρ ((s \ ⋃ (x ∈ h.t), h.u x) ∪ (⋃ (x ∈ h.t), h.u x)) :
    measure_mono (by simp only [subset_union_left, diff_union_self])
  ... ≤ ρ (s \ ⋃ (x ∈ h.t), h.u x) + ρ (⋃ (x ∈ h.t), h.u x) : measure_union_le _ _
  ... = ∑' (x : h.t), ρ (h.u x) : by rw [hρ h.measure_diff_bUnion,
    measure_bUnion h.t_countable h.u_disjoint (λ x hx, (h.is_closed_u hx).measurable_set), zero_add]

lemma measure_le_tsum [second_countable_topology α] [opens_measurable_space α] :
  μ s ≤ ∑' (x : h.t), μ (h.u x) :=
h.measure_le_tsum_of_absolutely_continuous measure.absolutely_continuous.rfl

end fine_subfamily_on

variable (v : vitali_family μ)
include v

/-- Given a vitali family `v`, then `v.filter_at x` is the filter on `set α` made of those families
that contain all sets of `v.sets_at x` of a sufficiently small diameter. This filter makes it
possible to express limiting behavior when sets in `v.sets_at x` shrink to `x`. -/
def filter_at (x : α) : filter (set α) :=
⨅ (ε ∈ Ioi (0 : ℝ)), 𝓟 {a ∈ v.sets_at x | a ⊆ closed_ball x ε}

/-- The limit along a Vitali family of `ρ a / μ a` where it makes sense, and garbage otherwise.
Do *not* use this definition: it is only a temporary device to show that this ratio tends almost
everywhere to the Radon-Nikodym derivative. -/
noncomputable def lim_ratio (ρ : measure α) (x : α) : ℝ≥0∞ :=
lim (v.filter_at x) (λ a, ρ a / μ a)

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

instance filter_at_ne_bot (x : α) : (v.filter_at x).ne_bot :=
begin
  simp only [ne_bot_iff, ←empty_mem_iff_bot, mem_filter_at_iff, not_exists, exists_prop,
    mem_empty_eq, and_true, gt_iff_lt, not_and, ne.def, not_false_iff, not_forall],
  assume ε εpos,
  obtain ⟨w, w_sets, hw⟩ : ∃ (w ∈ v.sets_at x), w ⊆ closed_ball x ε := v.nontrivial x ε εpos,
  exact ⟨w, w_sets, hw⟩
end

lemma eventually_filter_at_iff {x : α} {P : set α → Prop} :
  (∀ᶠ a in v.filter_at x, P a) ↔ ∃ (ε > (0 : ℝ)), ∀ a ∈ v.sets_at x, a ⊆ closed_ball x ε → P a :=
v.mem_filter_at_iff

lemma eventually_filter_at_mem_sets (x : α) :
  ∀ᶠ a in v.filter_at x, a ∈ v.sets_at x :=
begin
  simp only [eventually_filter_at_iff, exists_prop, and_true, gt_iff_lt,
             implies_true_iff] {contextual := tt},
  exact ⟨1, zero_lt_one⟩
end

lemma frequently_filter_at_iff {x : α} {P : set α → Prop} :
  (∃ᶠ a in v.filter_at x, P a) ↔ ∀ (ε > (0 : ℝ)), ∃ a ∈ v.sets_at x, a ⊆ closed_ball x ε ∧ P a :=
by simp only [filter.frequently, eventually_filter_at_iff, not_exists, exists_prop, not_and,
  not_not, not_forall]

lemma eventually_filter_at_subset_of_nhds {x : α} {o : set α} (hx : o ∈ 𝓝 x) :
  ∀ᶠ a in v.filter_at x, a ⊆ o :=
begin
  rw eventually_filter_at_iff,
  rcases metric.mem_nhds_iff.1 hx with ⟨ε, εpos, hε⟩,
  exact ⟨ε/2, half_pos εpos,
    λ a av ha, ha.trans ((closed_ball_subset_ball (half_lt_self εpos)).trans hε)⟩
end

lemma fine_subfamily_on_of_frequently (v : vitali_family μ) (f : α → set (set α)) (s : set α)
  (h : ∀ x ∈ s, ∃ᶠ a in v.filter_at x, a ∈ f x) :
  v.fine_subfamily_on f s :=
begin
  assume x hx ε εpos,
  obtain ⟨a, av, ha, af⟩ : ∃ (a : set α) (H : a ∈ v.sets_at x), a ⊆ closed_ball x ε ∧ a ∈ f x :=
    v.frequently_filter_at_iff.1 (h x hx) ε εpos,
  exact ⟨a, ⟨av, af⟩, ha⟩,
end

/-- For almost every point `x`, sufficiently small sets in a Vitali family around `x` have positive
measure. (This is a nontrivial result, following from the covering property of Vitali families). -/
theorem ae_eventually_measure_pos [second_countable_topology α] [opens_measurable_space α] :
  ∀ᵐ x ∂μ, ∀ᶠ a in v.filter_at x, 0 < μ a :=
begin
  set s := {x | ¬ (∀ᶠ a in v.filter_at x, 0 < μ a)} with hs,
  simp only [not_lt, not_eventually, nonpos_iff_eq_zero] at hs,
  change μ s = 0,
  let f : α → set (set α) := λ x, {a | μ a = 0},
  have h : v.fine_subfamily_on f s,
  { assume x hx ε εpos,
    rw hs at hx,
    simp only [frequently_filter_at_iff, exists_prop, gt_iff_lt, mem_set_of_eq] at hx,
    rcases hx ε εpos with ⟨a, a_sets, ax, μa⟩,
    exact ⟨a, ⟨a_sets, μa⟩, ax⟩ },
  refine le_antisymm _ bot_le,
  calc μ s ≤ ∑' (x : h.t), μ (h.u x) : h.measure_le_tsum
  ... = ∑' (x : h.t), 0 : by { congr, ext1 x, exact h.u_mem_f x.2 }
  ... = 0 : by simp only [tsum_zero, add_zero]
end

/-- For every point `x`, sufficiently small sets in a Vitali family around `x` have finite measure.
(This is a trivial result, following from the fact that the measure is locally finite). -/
theorem eventually_measure_lt_top [is_locally_finite_measure μ] (x : α) :
  ∀ᶠ a in v.filter_at x, μ a < ∞ :=
begin
  obtain ⟨ε, εpos, με⟩ : ∃ (ε : ℝ) (hi : 0 < ε), μ (closed_ball x ε) < ∞ :=
    (μ.finite_at_nhds x).exists_mem_basis nhds_basis_closed_ball,
  exact v.eventually_filter_at_iff.2 ⟨ε, εpos, λ a ha haε, (measure_mono haε).trans_lt με⟩,
end

/-- If two measures `ρ` and `ν` have, at every point of a set `s`, arbitrarily small sets in a
Vitali family satisfying `ρ a ≤ ν a`, then `ρ s ≤ ν s` if `ρ ≪ μ`.-/
theorem measure_le_of_frequently_le [sigma_compact_space α] [borel_space α]
  {ρ : measure α} (ν : measure α) [is_locally_finite_measure ν]
  (hρ : ρ ≪ μ) (s : set α) (hs : ∀ x ∈ s, ∃ᶠ a in v.filter_at x, ρ a ≤ ν a) :
  ρ s ≤ ν s :=
begin
  -- this follows from a covering argument using the sets satisfying `ρ a ≤ ν a`.
  apply ennreal.le_of_forall_pos_le_add (λ ε εpos hc, _),
  obtain ⟨U, sU, U_open, νU⟩ : ∃ (U : set α) (H : s ⊆ U), is_open U ∧ ν U ≤ ν s + ε :=
    exists_is_open_le_add s ν (ennreal.coe_pos.2 εpos).ne',
  let f : α → set (set α) := λ x, {a | ρ a ≤ ν a ∧ a ⊆ U},
  have h : v.fine_subfamily_on f s,
  { apply v.fine_subfamily_on_of_frequently f s (λ x hx, _),
    have := (hs x hx).and_eventually ((v.eventually_filter_at_mem_sets x).and
      (v.eventually_filter_at_subset_of_nhds (U_open.mem_nhds (sU hx)))),
    apply frequently.mono this,
    rintros a ⟨ρa, av, aU⟩,
    exact ⟨ρa, aU⟩ },
  haveI : encodable h.t := h.t_countable.to_encodable,
  calc ρ s ≤ ∑' (x : h.t), ρ (h.u x) : h.measure_le_tsum_of_absolutely_continuous hρ
  ... ≤ ∑' (x : h.t), ν (h.u x) : ennreal.tsum_le_tsum (λ x, (h.u_mem_f x.2).1)
  ... = ν (⋃ (x : h.t), h.u x) :
    by rw [measure_Union h.u_disjoint_subtype (λ i, (h.is_closed_u i.2).measurable_set)]
  ... ≤ ν U : measure_mono (Union_subset (λ i, (h.u_mem_f i.2).2))
  ... ≤ ν s + ε : νU
end

section

variables [sigma_compact_space α] [borel_space α] [is_locally_finite_measure μ]
  {ρ : measure α} [is_locally_finite_measure ρ]

/-- If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`, the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`. -/
lemma ae_eventually_measure_zero_of_singular (hρ : ρ ⊥ₘ μ) :
  ∀ᵐ x ∂μ, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 0) :=
begin
  have A : ∀ ε > (0 : ℝ≥0), ∀ᵐ x ∂μ, ∀ᶠ a in v.filter_at x, ρ a < ε * μ a,
  { assume ε εpos,
    set s := {x | ¬(∀ᶠ a in v.filter_at x, ρ a < ε * μ a) } with hs,
    change μ s = 0,
    obtain ⟨o, o_meas, ρo, μo⟩ : ∃ (o : set α), measurable_set o ∧ ρ o = 0 ∧ μ oᶜ = 0 := hρ,
    apply le_antisymm _ bot_le,
    calc μ s ≤ μ ((s ∩ o) ∪ oᶜ) : begin
      conv_lhs { rw ← inter_union_compl s o },
      exact measure_mono (union_subset_union_right _ (inter_subset_right _ _))
    end
    ... ≤ μ (s ∩ o) + μ (oᶜ) : measure_union_le _ _
    ... = μ (s ∩ o) : by rw [μo, add_zero]
    ... = ε⁻¹ * (ε • μ) (s ∩ o) : begin
      simp only [coe_nnreal_smul_apply, ← mul_assoc, mul_comm _ (ε : ℝ≥0∞)],
      rw [ennreal.mul_inv_cancel (ennreal.coe_pos.2 εpos).ne' ennreal.coe_ne_top, one_mul],
    end
    ... ≤ ε⁻¹ * ρ (s ∩ o) : begin
      apply ennreal.mul_le_mul le_rfl,
      refine v.measure_le_of_frequently_le ρ ((measure.absolutely_continuous.refl μ).smul ε) _ _,
      assume x hx,
      rw hs at hx,
      simp only [mem_inter_eq, not_lt, not_eventually, mem_set_of_eq] at hx,
      exact hx.1
    end
    ... ≤ ε⁻¹ * ρ o : ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_right _ _))
    ... = 0 : by rw [ρo, mul_zero] },
  obtain ⟨u, u_anti, u_pos, u_lim⟩ :
    ∃ (u : ℕ → ℝ≥0), strict_anti u ∧ (∀ (n : ℕ), 0 < u n) ∧ tendsto u at_top (𝓝 0) :=
      exists_seq_strict_anti_tendsto (0 : ℝ≥0),
  have B : ∀ᵐ x ∂μ, ∀ n, ∀ᶠ a in v.filter_at x, ρ a < u n * μ a :=
    ae_all_iff.2 (λ n, A (u n) (u_pos n)),
  filter_upwards [B, v.ae_eventually_measure_pos],
  assume x hx h'x,
  refine tendsto_order.2 ⟨λ z hz, (ennreal.not_lt_zero hz).elim, λ z hz, _⟩,
  obtain ⟨w, w_pos, w_lt⟩ : ∃ (w : ℝ≥0), (0 : ℝ≥0∞) < w ∧ (w : ℝ≥0∞) < z :=
    ennreal.lt_iff_exists_nnreal_btwn.1 hz,
  obtain ⟨n, hn⟩ : ∃ n, u n < w :=
    ((tendsto_order.1 u_lim).2 w (ennreal.coe_pos.1 w_pos)).exists,
  filter_upwards [hx n, h'x, v.eventually_measure_lt_top x],
  assume a ha μa_pos μa_lt_top,
  rw ennreal.div_lt_iff (or.inl μa_pos.ne') (or.inl μa_lt_top.ne),
  exact ha.trans_le (ennreal.mul_le_mul ((ennreal.coe_le_coe.2 hn.le).trans w_lt.le) le_rfl)
end

section absolutely_continuous

variable (hρ : ρ ≪ μ)
include hρ

/-- A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbitrarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction if `0 < μ s`. -/
theorem null_of_frequently_le_of_frequently_ge {c d : ℝ≥0} (hcd : c < d) (s : set α)
  (hc : ∀ x ∈ s, ∃ᶠ a in v.filter_at x, ρ a ≤ c * μ a)
  (hd : ∀ x ∈ s, ∃ᶠ a in v.filter_at x, (d : ℝ≥0∞) * μ a ≤ ρ a) :
  μ s = 0 :=
begin
  apply null_of_locally_null s (λ x hx, _),
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : set α, x ∈ o ∧ is_open o ∧ μ o < ∞ :=
    measure.exists_is_open_measure_lt_top μ x,
  refine ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), _⟩,
  let s' := s ∩ o,
  by_contra,
  apply lt_irrefl (ρ s'),
  calc ρ s' ≤ c * μ s' : v.measure_le_of_frequently_le (c • μ) hρ s' (λ x hx, hc x hx.1)
  ... < d * μ s' : begin
    apply (ennreal.mul_lt_mul_right h _).2 (ennreal.coe_lt_coe.2 hcd),
    exact (lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) μo).ne,
  end
  ... ≤ ρ s' : v.measure_le_of_frequently_le ρ
    ((measure.absolutely_continuous.refl μ).smul d) s' (λ x hx, hd x hx.1)
end

/-- If `ρ` is absolutely continuous with respect to `μ`, then for almost every `x`, the
ratio `ρ a / μ a` converges to a finite limit as `a` shrinks to `x` along a
Vitali family for `μ`. -/
theorem ae_tendsto_div :
  ∀ᵐ x ∂μ, ∃ c, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 c) :=
begin
  let w : set ℝ≥0∞ := {x | ∃ a : ℚ, x = ennreal.of_real a},
  have w_count : countable w,
  { have : w = range (λ (a : ℚ), ennreal.of_real a),
      by { ext x, simp only [eq_comm, mem_range, mem_set_of_eq] },
    rw this,
    exact countable_range _ },
  have w_dense : dense w,
  { refine dense_iff_forall_lt_exists_mem.2 (λ c d hcd, _),
    rcases ennreal.lt_iff_exists_rat_btwn.1 hcd with ⟨q, hq⟩,
    exact ⟨ennreal.of_real q, ⟨q, rfl⟩, hq.2⟩ },
  have A : ∀ (c ∈ w) (d ∈ w), (c < d) → ∀ᵐ x ∂μ,
    ¬((∃ᶠ a in v.filter_at x, ρ a / μ a < c) ∧ (∃ᶠ a in v.filter_at x, d < ρ a / μ a)),
  { assume c hc d hd hcd,
    rcases hc with ⟨c, rfl⟩,
    rcases hd with ⟨d, rfl⟩,
    apply v.null_of_frequently_le_of_frequently_ge hρ (ennreal.coe_lt_coe.1 hcd),
    { simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_set_of_eq, mem_compl_eq, not_forall],
      assume x h1x h2x,
      apply h1x.mono (λ a ha, _),
      refine (ennreal.div_le_iff_le_mul _ (or.inr _)).1 ha.le,
      { simp only [ennreal.coe_ne_top, ne.def, or_true, not_false_iff] },
      { suffices : 0 < ennreal.of_real c, by simpa only [rat.cast_pos, real.to_nnreal_eq_zero,
          ennreal.of_real_pos, not_le, ennreal.coe_eq_zero, ne.def],
        exact bot_le.trans_lt ha } },
    { simp only [and_imp, exists_prop, not_frequently, not_and, not_lt, not_le, not_eventually,
        mem_set_of_eq, mem_compl_eq, not_forall],
      assume x h1x h2x,
      apply h2x.mono (λ a ha, _),
      exact ennreal.mul_le_of_le_div ha.le } },
  have B : ∀ᵐ x ∂μ, ∀ (c ∈ w) (d ∈ w), (c < d) →
    ¬((∃ᶠ a in v.filter_at x, ρ a / μ a < c) ∧ (∃ᶠ a in v.filter_at x, d < ρ a / μ a)),
    by simpa only [ae_ball_iff w_count, ae_imp_iff],
  filter_upwards [B],
  assume x hx,
  exact tendsto_of_no_upcrossings w_dense hx,
end

lemma ae_tendsto_lim_ratio :
  ∀ᵐ x ∂μ, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio ρ x)) :=
begin
  filter_upwards [v.ae_tendsto_div hρ],
  assume x hx,
  exact tendsto_nhds_lim hx,
end

/-- Given two thresholds `p < q`, the sets `{x | v.lim_ratio ρ x < p}`
and `{x | q < v.lim_ratio ρ x}` are obviously disjoint. The key to proving that `v.lim_ratio ρ` is
almost everywhere measurable is to show that these sets have measurable supersets which are also
disjoint, up to zero measure. This is the content of this lemma. -/
lemma exists_measurable_supersets_lim_ratio {p q : ℝ≥0} (hpq : p < q) :
  ∃ a b, measurable_set a ∧ measurable_set b ∧ {x | v.lim_ratio ρ x < p} ⊆ a
    ∧ {x | (q : ℝ≥0∞) < v.lim_ratio ρ x} ⊆ b ∧ μ (a ∩ b) = 0 :=
begin
  /- Here is a rough sketch, assuming that the measure is finite and the limit is well defined
  everywhere. Let `u := {x | v.lim_ratio ρ x < p}` and `w := {x | q < v.lim_ratio ρ x}`. They
  have measurable supersets `u'` and `w'` of the same measure. We will show that these satisfy
  the conclusion of the theorem, i.e., `μ (u' ∩ w') = 0`. For this, note that
  `ρ (u' ∩ w') = ρ (u ∩ w')` (as `w'` is measurable, see `measure_to_measurable_add_inter_left`).
  The latter set is included in the set where the limit of the ratios is `< p`, and therefore
  its measure is `≤ p * μ (u ∩ w')`. Using the same trick in the other direction gives that this is
  `p * μ (u' ∩ w')`. We have shown that `ρ (u' ∩ w') ≤ p * μ (u' ∩ w')`. Arguing in the same way but
  using the `w` part gives `q * μ (u' ∩ w') ≤ ρ (u' ∩ w')`. If `μ (u' ∩ w')` were nonzero, this
  would be a contradiction as `p < q`.

  For the rigorous proof, we need to work on a part of the space where the measure is finite
  (provided by `spanning_sets (ρ + μ)`) and to restrict to the set where the limit is well defined
  (called `s` below, of full measure). Otherwise, the argument goes through.
  -/
  let s := {x | ∃ c, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 c)},
  let o : ℕ → set α := spanning_sets (ρ + μ),
  let u := λ n, (s ∩ {x | v.lim_ratio ρ x < p} ∩ o n),
  let w := λ n, (s ∩ {x | (q : ℝ≥0∞) < v.lim_ratio ρ x} ∩ o n),
  -- the supersets are obtained by restricting to the set `s` where the limit is well defined, to
  -- a finite measure part `o n`, taking a measurable superset here, and then taking the union over
  -- `n`.
  refine ⟨to_measurable μ sᶜ ∪ (⋃ n, to_measurable (ρ + μ) (u n)),
    to_measurable μ sᶜ ∪ (⋃ n, to_measurable (ρ + μ) (w n)), _, _, _, _, _⟩,
  -- check that these sets are measurable supersets as required
  { exact (measurable_set_to_measurable _ _).union
      (measurable_set.Union (λ n, (measurable_set_to_measurable _ _))) },
  { exact (measurable_set_to_measurable _ _).union
      (measurable_set.Union (λ n, (measurable_set_to_measurable _ _))) },
  { assume x hx,
    by_cases h : x ∈ s,
    { refine or.inr (mem_Union.2 ⟨spanning_sets_index (ρ + μ) x, _⟩),
      exact subset_to_measurable _ _ ⟨⟨h, hx⟩, mem_spanning_sets_index _ _⟩ },
    { exact or.inl (subset_to_measurable μ sᶜ h) } },
  { assume x hx,
    by_cases h : x ∈ s,
    { refine or.inr (mem_Union.2 ⟨spanning_sets_index (ρ + μ) x, _⟩),
      exact subset_to_measurable _ _ ⟨⟨h, hx⟩, mem_spanning_sets_index _ _⟩ },
    { exact or.inl (subset_to_measurable μ sᶜ h) } },
  -- it remains to check the nontrivial part that these sets have zero measure intersection
  -- it suffices to do it for fixed `m` and `n`, as one is taking countable unions.
  suffices H : ∀ (m n : ℕ), μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) = 0,
  { have A : (to_measurable μ sᶜ ∪ (⋃ n, to_measurable (ρ + μ) (u n))) ∩
      (to_measurable μ sᶜ ∪ (⋃ n, to_measurable (ρ + μ) (w n))) ⊆
      to_measurable μ sᶜ ∪ (⋃ m n, (to_measurable (ρ + μ) (u m)) ∩ (to_measurable (ρ + μ) (w n))),
    { simp only [inter_distrib_left, inter_distrib_right, true_and, subset_union_left,
        union_subset_iff, inter_self],
      refine ⟨_, _, _⟩,
      { exact (inter_subset_left _ _).trans (subset_union_left _ _) },
      { exact (inter_subset_right _ _).trans (subset_union_left _ _) },
      { simp_rw [Union_inter, inter_Union], exact subset_union_right _ _ } },
    refine le_antisymm ((measure_mono A).trans _) bot_le,
    calc
    μ (to_measurable μ sᶜ ∪ (⋃ m n, (to_measurable (ρ + μ) (u m)) ∩ (to_measurable (ρ + μ) (w n))))
    ≤ μ (to_measurable μ sᶜ)
        + μ (⋃ m n, (to_measurable (ρ + μ) (u m)) ∩ (to_measurable (ρ + μ) (w n))) :
      measure_union_le _ _
    ... = μ (⋃ m n, (to_measurable (ρ + μ) (u m)) ∩ (to_measurable (ρ + μ) (w n))) :
      by { have : μ sᶜ = 0 := v.ae_tendsto_div hρ, rw [measure_to_measurable, this, zero_add] }
    ... ≤ ∑' m n, μ ((to_measurable (ρ + μ) (u m)) ∩ (to_measurable (ρ + μ) (w n))) :
      (measure_Union_le _).trans (ennreal.tsum_le_tsum (λ m, measure_Union_le _))
    ... = 0 : by simp only [H, tsum_zero] },
  -- now starts the nontrivial part of the argument. We fix `m` and `n`, and show that the
  -- measurable supersets of `u m` and `w n` have zero measure intersection by using the lemmas
  -- `measure_to_measurable_add_inter_left` (to reduce to `u m` or `w n` instead of the measurable
  -- superset) and `measure_le_of_frequently_le` to compare their measures for `ρ` and `μ`.
  assume m n,
  have I : (ρ + μ) (u m) ≠ ∞,
  { apply (lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top (ρ + μ) m)).ne,
    exact inter_subset_right _ _ },
  have J : (ρ + μ) (w n) ≠ ∞,
  { apply (lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top (ρ + μ) n)).ne,
    exact inter_subset_right _ _ },
  have A : ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))
            ≤ p * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) := calc
    ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))
        = ρ (u m ∩ to_measurable (ρ + μ) (w n)) :
          measure_to_measurable_add_inter_left (measurable_set_to_measurable _ _) I
    ... ≤ (p • μ) (u m ∩ to_measurable (ρ + μ) (w n)) : begin
        refine v.measure_le_of_frequently_le _ hρ _ (λ x hx, _),
        have L : tendsto (λ (a : set α), ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio ρ x)) :=
          tendsto_nhds_lim hx.1.1.1,
        have I : ∀ᶠ (b : set α) in v.filter_at x, ρ b / μ b < p :=
          (tendsto_order.1 L).2 _ hx.1.1.2,
        apply I.frequently.mono (λ a ha, _),
        rw [coe_nnreal_smul_apply],
        refine (ennreal.div_le_iff_le_mul _ (or.inr (bot_le.trans_lt ha).ne')).1 ha.le,
        simp only [ennreal.coe_ne_top, ne.def, or_true, not_false_iff]
      end
    ... = p * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) :
       by simp only [coe_nnreal_smul_apply,
          (measure_to_measurable_add_inter_right (measurable_set_to_measurable _ _) I)],
  have B : (q : ℝ≥0∞) * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))
              ≤ ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) := calc
    (q : ℝ≥0∞) * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))
        = (q : ℝ≥0∞) * μ (to_measurable (ρ + μ) (u m) ∩ w n) : begin
        conv_rhs { rw inter_comm }, rw inter_comm,
        rw measure_to_measurable_add_inter_right (measurable_set_to_measurable _ _) J,
      end
    ... ≤ ρ (to_measurable (ρ + μ) (u m) ∩ w n) : begin
        rw [← coe_nnreal_smul_apply],
        refine v.measure_le_of_frequently_le _ (absolutely_continuous.rfl.coe_nnreal_smul _) _ _,
        assume x hx,
        have L : tendsto (λ (a : set α), ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio ρ x)) :=
          tendsto_nhds_lim hx.2.1.1,
        have I : ∀ᶠ (b : set α) in v.filter_at x, (q : ℝ≥0∞) < ρ b / μ b :=
          (tendsto_order.1 L).1 _ hx.2.1.2,
        apply I.frequently.mono (λ a ha, _),
        rw [coe_nnreal_smul_apply],
        exact ennreal.mul_le_of_le_div ha.le
      end
    ... = ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) : begin
        rw inter_comm, conv_rhs { rw inter_comm },
        exact (measure_to_measurable_add_inter_left (measurable_set_to_measurable _ _) J).symm,
      end,
  by_contra,
  apply lt_irrefl (ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))),
  calc ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n))
      ≤ p * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) : A
  ... < q * μ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) : begin
    apply (ennreal.mul_lt_mul_right h _).2 (ennreal.coe_lt_coe.2 hpq),
    suffices H : (ρ + μ) (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) ≠ ∞,
    { simp only [not_or_distrib, ennreal.add_eq_top, pi.add_apply, ne.def, coe_add] at H,
      exact H.2 },
    apply (lt_of_le_of_lt (measure_mono (inter_subset_left _ _)) _).ne,
    rw measure_to_measurable,
    apply lt_of_le_of_lt (measure_mono _) (measure_spanning_sets_lt_top (ρ + μ) m),
    exact inter_subset_right _ _
  end
  ... ≤ ρ (to_measurable (ρ + μ) (u m) ∩ to_measurable (ρ + μ) (w n)) : B
end

theorem ae_measurable_lim_ratio : ae_measurable (v.lim_ratio ρ) μ :=
begin
  apply ennreal.ae_measurable_of_exist_almost_disjoint_supersets _ _ (λ p q hpq, _),
  exact v.exists_measurable_supersets_lim_ratio hρ hpq,
end

/-- A measurable version of `v.lim_ratio ρ`. Do *not* use this definition: it is only a temporary
device to show that `v.lim_ratio` is almost everywhere equal to the Radon-Nikodym derivative. -/
noncomputable def lim_ratio_meas : α → ℝ≥0∞ :=
(v.ae_measurable_lim_ratio hρ).mk _

lemma lim_ratio_meas_measurable : measurable (v.lim_ratio_meas hρ) :=
ae_measurable.measurable_mk _

lemma ae_tendsto_lim_ratio_meas :
  ∀ᵐ x ∂μ, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio_meas hρ x)) :=
begin
  filter_upwards [v.ae_tendsto_lim_ratio hρ, ae_measurable.ae_eq_mk (v.ae_measurable_lim_ratio hρ)],
  assume x hx h'x,
  rwa h'x at hx,
end

lemma measure_le_mul_of_subset_lim_ratio_meas_lt
  {p : ℝ≥0} {s : set α} (h : s ⊆ {x | v.lim_ratio_meas hρ x < p}) :
  ρ s ≤ p * μ s :=
begin
  let t := {x : α | tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio_meas hρ x))},
  have A : μ tᶜ = 0 := v.ae_tendsto_lim_ratio_meas hρ,
  suffices H : ρ (s ∩ t) ≤ (p • μ) (s ∩ t), from calc
    ρ s = ρ ((s ∩ t) ∪ (s ∩ tᶜ)) : by rw inter_union_compl
    ... ≤ ρ (s ∩ t) + ρ (s ∩ tᶜ) : measure_union_le _ _
    ... ≤ p * μ (s ∩ t) + 0 :
      add_le_add H ((measure_mono (inter_subset_right _ _)).trans (hρ A).le)
    ... ≤ p * μ s :
      by { rw add_zero, exact ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_left _ _)) },
  refine v.measure_le_of_frequently_le _ hρ _ (λ x hx, _),
  have I : ∀ᶠ (b : set α) in v.filter_at x, ρ b / μ b < p := (tendsto_order.1 hx.2).2 _ (h hx.1),
  apply I.frequently.mono (λ a ha, _),
  rw [coe_nnreal_smul_apply],
  refine (ennreal.div_le_iff_le_mul _ (or.inr (bot_le.trans_lt ha).ne')).1 ha.le,
  simp only [ennreal.coe_ne_top, ne.def, or_true, not_false_iff]
end

lemma mul_measure_le_of_subset_lt_lim_ratio_meas
  {q : ℝ≥0} {s : set α} (h : s ⊆ {x | (q : ℝ≥0∞) < v.lim_ratio_meas hρ x}) :
  (q : ℝ≥0∞) * μ s ≤ ρ s :=
begin
  let t := {x : α | tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (v.lim_ratio_meas hρ x))},
  have A : μ tᶜ = 0 := v.ae_tendsto_lim_ratio_meas hρ,
  suffices H : (q • μ) (s ∩ t) ≤ ρ (s ∩ t), from calc
    (q • μ) s = (q • μ) ((s ∩ t) ∪ (s ∩ tᶜ)) : by rw inter_union_compl
    ... ≤ (q • μ) (s ∩ t) + (q • μ) (s ∩ tᶜ) : measure_union_le _ _
    ... ≤ ρ (s ∩ t) + q * μ tᶜ : begin
        apply add_le_add H,
        rw [coe_nnreal_smul_apply],
        exact ennreal.mul_le_mul le_rfl (measure_mono (inter_subset_right _ _)),
      end
    ... ≤ ρ s :
      by { rw [A, mul_zero, add_zero], exact measure_mono (inter_subset_left _ _) },
  refine v.measure_le_of_frequently_le _ (absolutely_continuous.rfl.coe_nnreal_smul _) _ _,
  assume x hx,
  have I : ∀ᶠ a in v.filter_at x, (q : ℝ≥0∞) < ρ a / μ a := (tendsto_order.1 hx.2).1 _ (h hx.1),
  apply I.frequently.mono (λ a ha, _),
  rw [coe_nnreal_smul_apply],
  exact ennreal.mul_le_of_le_div ha.le
end

lemma measure_lim_ratio_meas_top : μ {x | v.lim_ratio_meas hρ x = ∞} = 0 :=
begin
  refine null_of_locally_null _ (λ x hx, _),
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : set α, x ∈ o ∧ is_open o ∧ ρ o < ∞ :=
    measure.exists_is_open_measure_lt_top ρ x,
  refine ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), le_antisymm _ bot_le⟩,
  let s := {x : α | v.lim_ratio_meas hρ x = ∞} ∩ o,
  have ρs : ρ s ≠ ∞ := ((measure_mono (inter_subset_right _ _)).trans_lt μo).ne,
  have A : ∀ (q : ℝ≥0), 1 ≤ q → μ s ≤ q⁻¹ * ρ s,
  { assume q hq,
    rw [mul_comm, ← div_eq_mul_inv, ennreal.le_div_iff_mul_le _ (or.inr ρs), mul_comm],
    { apply v.mul_measure_le_of_subset_lt_lim_ratio_meas hρ,
      assume y hy,
      have : v.lim_ratio_meas hρ y = ∞ := hy.1,
      simp only [this, ennreal.coe_lt_top, mem_set_of_eq], },
    { simp only [(zero_lt_one.trans_le hq).ne', true_or, ennreal.coe_eq_zero, ne.def,
        not_false_iff] } },
  have B : tendsto (λ (q : ℝ≥0), (q : ℝ≥0∞)⁻¹ * ρ s) at_top (𝓝 (∞⁻¹ * ρ s)),
  { apply ennreal.tendsto.mul_const _ (or.inr ρs),
    apply ennreal.tendsto_inv_iff.2 (ennreal.tendsto_coe_nhds_top.2 tendsto_id) },
  simp only [zero_mul, ennreal.inv_top] at B,
  apply ge_of_tendsto B,
  exact eventually_at_top.2 ⟨1, A⟩,
end

lemma measure_lim_ratio_meas_zero : ρ {x | v.lim_ratio_meas hρ x = 0} = 0 :=
begin
  refine null_of_locally_null _ (λ x hx, _),
  obtain ⟨o, xo, o_open, μo⟩ : ∃ o : set α, x ∈ o ∧ is_open o ∧ μ o < ∞ :=
    measure.exists_is_open_measure_lt_top μ x,
  refine ⟨o, mem_nhds_within_of_mem_nhds (o_open.mem_nhds xo), le_antisymm _ bot_le⟩,
  let s := {x : α | v.lim_ratio_meas hρ x = 0} ∩ o,
  have μs : μ s ≠ ∞ := ((measure_mono (inter_subset_right _ _)).trans_lt μo).ne,
  have A : ∀ (q : ℝ≥0), 0 < q → ρ s ≤ q * μ s,
  { assume q hq,
    apply v.measure_le_mul_of_subset_lim_ratio_meas_lt hρ,
    assume y hy,
    have : v.lim_ratio_meas hρ y = 0 := hy.1,
    simp only [this, mem_set_of_eq, hq, ennreal.coe_pos], },
  have B : tendsto (λ (q : ℝ≥0), (q : ℝ≥0∞) * μ s) (𝓝[Ioi (0 : ℝ≥0)] 0) (𝓝 ((0 : ℝ≥0) * μ s)),
  { apply ennreal.tendsto.mul_const _ (or.inr μs),
    rw ennreal.tendsto_coe,
    exact nhds_within_le_nhds },
  simp only [zero_mul, ennreal.coe_zero] at B,
  apply ge_of_tendsto B,
  filter_upwards [self_mem_nhds_within],
  exact A
end

lemma with_density_le_mul {s : set α} (hs : measurable_set s) {t : ℝ≥0} (ht : 1 < t) :
  μ.with_density (v.lim_ratio_meas hρ) s ≤ t^2 * ρ s :=
begin
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne',
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0, by simpa only [ennreal.coe_eq_zero, ne.def] using t_ne_zero',
  let ν := μ.with_density (v.lim_ratio_meas hρ),
  let f := v.lim_ratio_meas hρ,
  have f_meas : measurable f := v.lim_ratio_meas_measurable hρ,
  have A : ν (s ∩ f ⁻¹' ({0})) ≤ ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' {0}),
  { apply le_trans _ (zero_le _),
    have M : measurable_set (s ∩ f ⁻¹' ({0})) := hs.inter (f_meas (measurable_set_singleton _)),
    simp only [ν, f, nonpos_iff_eq_zero, M, with_density_apply, lintegral_eq_zero_iff f_meas],
    apply (ae_restrict_iff' M).2,
    exact eventually_of_forall (λ x hx, hx.2) },
  have B : ν (s ∩ f ⁻¹' ({∞})) ≤ ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' {∞}),
  { apply le_trans (le_of_eq _) (zero_le _),
    apply with_density_absolutely_continuous μ _,
    rw ← nonpos_iff_eq_zero,
    exact (measure_mono (inter_subset_right _ _)).trans (v.measure_lim_ratio_meas_top hρ).le },
  have C : ∀ (n : ℤ), ν (s ∩ f⁻¹' (Ico (t^n) (t^(n+1))))
                        ≤ ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))),
  { assume n,
    let I := Ico ((t : ℝ≥0∞)^n) (t^(n+1)),
    have M : measurable_set (s ∩ f ⁻¹' I) := hs.inter (f_meas measurable_set_Ico),
    simp only [f, M, with_density_apply, coe_nnreal_smul_apply],
    calc
    ∫⁻ x in s ∩ f⁻¹' I, f x ∂μ
        ≤ ∫⁻ x in s ∩ f⁻¹' I, t^(n+1) ∂μ :
          lintegral_mono_ae ((ae_restrict_iff' M).2 (eventually_of_forall (λ x hx, hx.2.2.le)))
    ... = t^(n+1) * μ (s ∩ f⁻¹' I) :
          by simp only [lintegral_const, measurable_set.univ, measure.restrict_apply, univ_inter]
    ... = t^(2 : ℤ) * (t^(n-1) * μ (s ∩ f⁻¹' I)) : begin
        rw [← mul_assoc, ← ennreal.zpow_add t_ne_zero ennreal.coe_ne_top],
        congr' 2,
        abel,
      end
    ... ≤ t^2 * ρ (s ∩ f ⁻¹' I) : begin
        apply ennreal.mul_le_mul le_rfl _,
        rw ← ennreal.coe_zpow (zero_lt_one.trans ht).ne',
        apply v.mul_measure_le_of_subset_lt_lim_ratio_meas hρ,
        assume x hx,
        apply lt_of_lt_of_le _ hx.2.1,
        rw [← ennreal.coe_zpow (zero_lt_one.trans ht).ne', ennreal.coe_lt_coe, sub_eq_add_neg,
          zpow_add₀ t_ne_zero'],
        conv_rhs { rw ← mul_one (t^ n) },
        refine mul_lt_mul' le_rfl _ (zero_le _) (nnreal.zpow_pos t_ne_zero' _),
        rw zpow_neg_one₀,
        exact nnreal.inv_lt_one ht,
      end },
  calc ν s = ν (s ∩ f⁻¹' {0}) + ν (s ∩ f⁻¹' {∞}) + ∑' (n : ℤ), ν (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))) :
    measure_eq_measure_preimage_add_measure_tsum_Ico_pow ν f_meas hs ht
  ... ≤ ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' {0}) + ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' {∞})
          + ∑' (n : ℤ), ((t : ℝ≥0∞)^2 • ρ) (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))) :
            add_le_add (add_le_add A B) (ennreal.tsum_le_tsum C)
  ... = ((t : ℝ≥0∞)^2 • ρ) s :
    (measure_eq_measure_preimage_add_measure_tsum_Ico_pow ((t : ℝ≥0∞)^2 • ρ) f_meas hs ht).symm
end

lemma le_mul_with_density {s : set α} (hs : measurable_set s) {t : ℝ≥0} (ht : 1 < t) :
  ρ s ≤ t * μ.with_density (v.lim_ratio_meas hρ) s :=
begin
  have t_ne_zero' : t ≠ 0 := (zero_lt_one.trans ht).ne',
  have t_ne_zero : (t : ℝ≥0∞) ≠ 0, by simpa only [ennreal.coe_eq_zero, ne.def] using t_ne_zero',
  let ν := μ.with_density (v.lim_ratio_meas hρ),
  let f := v.lim_ratio_meas hρ,
  have f_meas : measurable f := v.lim_ratio_meas_measurable hρ,
  have A : ρ (s ∩ f ⁻¹' ({0})) ≤ (t • ν) (s ∩ f⁻¹' {0}),
  { refine le_trans (measure_mono (inter_subset_right _ _)) (le_trans (le_of_eq _) (zero_le _)),
    exact v.measure_lim_ratio_meas_zero hρ },
  have B : ρ (s ∩ f ⁻¹' ({∞})) ≤ (t • ν) (s ∩ f⁻¹' {∞}),
  { apply le_trans (le_of_eq _) (zero_le _),
    apply hρ,
    rw ← nonpos_iff_eq_zero,
    exact (measure_mono (inter_subset_right _ _)).trans (v.measure_lim_ratio_meas_top hρ).le },
  have C : ∀ (n : ℤ), ρ (s ∩ f⁻¹' (Ico (t^n) (t^(n+1))))
                        ≤ (t • ν) (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))),
  { assume n,
    let I := Ico ((t : ℝ≥0∞)^n) (t^(n+1)),
    have M : measurable_set (s ∩ f ⁻¹' I) := hs.inter (f_meas measurable_set_Ico),
    simp only [f, M, with_density_apply, coe_nnreal_smul_apply],
    calc ρ (s ∩ f ⁻¹' I) ≤ t^ (n+1) * μ (s ∩ f ⁻¹' I) : begin
        rw ← ennreal.coe_zpow t_ne_zero',
        apply v.measure_le_mul_of_subset_lim_ratio_meas_lt hρ,
        assume x hx,
        apply hx.2.2.trans_le (le_of_eq _),
        rw ennreal.coe_zpow t_ne_zero',
      end
    ... = ∫⁻ x in s ∩ f⁻¹' I, t^(n+1) ∂μ :
      by simp only [lintegral_const, measurable_set.univ, measure.restrict_apply, univ_inter]
    ... ≤ ∫⁻ x in s ∩ f⁻¹' I, t * f x ∂μ : begin
        apply lintegral_mono_ae ((ae_restrict_iff' M).2 (eventually_of_forall (λ x hx, _))),
        rw [add_comm, ennreal.zpow_add t_ne_zero ennreal.coe_ne_top, zpow_one],
        exact ennreal.mul_le_mul le_rfl hx.2.1,
      end
    ... = t * ∫⁻ x in s ∩ f⁻¹' I, f x ∂μ : lintegral_const_mul _ f_meas },
  calc ρ s = ρ (s ∩ f⁻¹' {0}) + ρ (s ∩ f⁻¹' {∞}) + ∑' (n : ℤ), ρ (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))) :
    measure_eq_measure_preimage_add_measure_tsum_Ico_pow ρ f_meas hs ht
  ... ≤ (t • ν) (s ∩ f⁻¹' {0}) + (t • ν) (s ∩ f⁻¹' {∞})
          + ∑' (n : ℤ), (t • ν) (s ∩ f⁻¹' (Ico (t^n) (t^(n+1)))) :
            add_le_add (add_le_add A B) (ennreal.tsum_le_tsum C)
  ... = (t • ν) s :
    (measure_eq_measure_preimage_add_measure_tsum_Ico_pow (t • ν) f_meas hs ht).symm
end

theorem with_density_lim_ratio_meas_eq : μ.with_density (v.lim_ratio_meas hρ) = ρ :=
begin
  ext1 s hs,
  refine le_antisymm _ _,
  { have : tendsto (λ (t : ℝ≥0), (t^2 * ρ s : ℝ≥0∞)) (𝓝[Ioi 1] 1) (𝓝 ((1 : ℝ≥0)^2 * ρ s)),
    { refine ennreal.tendsto.mul _ _ tendsto_const_nhds _,
      { exact ennreal.tendsto.pow (ennreal.tendsto_coe.2 nhds_within_le_nhds) },
      { simp only [one_pow, ennreal.coe_one, true_or, ne.def, not_false_iff, one_ne_zero] },
      { simp only [one_pow, ennreal.coe_one, ne.def, or_true, ennreal.one_ne_top,
                   not_false_iff] } },
    simp only [one_pow, one_mul, ennreal.coe_one] at this,
    refine ge_of_tendsto this _,
    filter_upwards [self_mem_nhds_within],
    assume t ht,
    exact v.with_density_le_mul hρ hs ht },
  { have : tendsto (λ (t : ℝ≥0), (t : ℝ≥0∞) * μ.with_density (v.lim_ratio_meas hρ) s) (𝓝[Ioi 1] 1)
            (𝓝 ((1 : ℝ≥0) * μ.with_density (v.lim_ratio_meas hρ) s)),
    { refine ennreal.tendsto.mul_const (ennreal.tendsto_coe.2 nhds_within_le_nhds) _,
      simp only [ennreal.coe_one, true_or, ne.def, not_false_iff, one_ne_zero], },
    simp only [one_mul, ennreal.coe_one] at this,
    refine ge_of_tendsto this _,
    filter_upwards [self_mem_nhds_within],
    assume t ht,
    exact v.le_mul_with_density hρ hs ht }
end

theorem ae_tendsto_rn_deriv_of_absolutely_continuous :
  ∀ᵐ x ∂μ, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (ρ.rn_deriv μ x)) :=
begin
  have A : (μ.with_density (v.lim_ratio_meas hρ)).rn_deriv μ =ᵐ[μ] v.lim_ratio_meas hρ :=
    rn_deriv_with_density μ (v.lim_ratio_meas_measurable hρ),
  rw v.with_density_lim_ratio_meas_eq hρ at A,
  filter_upwards [v.ae_tendsto_lim_ratio_meas hρ, A],
  assume x hx h'x,
  rwa h'x,
end

end absolutely_continuous

theorem ae_tendsto_rn_deriv :
  ∀ᵐ x ∂μ, tendsto (λ a, ρ a / μ a) (v.filter_at x) (𝓝 (ρ.rn_deriv μ x)) :=
begin
  let t := μ.with_density (ρ.rn_deriv μ),
  have eq_add : ρ = singular_part ρ μ + t := have_lebesgue_decomposition_add _ _,
  have A : ∀ᵐ x ∂μ, tendsto (λ a, singular_part ρ μ a / μ a) (v.filter_at x) (𝓝 0) :=
    v.ae_eventually_measure_zero_of_singular (mutually_singular_singular_part ρ μ),
  have B : ∀ᵐ x ∂μ, t.rn_deriv μ x = ρ.rn_deriv μ x :=
    rn_deriv_with_density μ (measurable_rn_deriv ρ μ),
  have C : ∀ᵐ x ∂μ, tendsto (λ a, t a / μ a) (v.filter_at x) (𝓝 (t.rn_deriv μ x)) :=
    v.ae_tendsto_rn_deriv_of_absolutely_continuous (with_density_absolutely_continuous _ _),
  filter_upwards [A, B, C],
  assume x Ax Bx Cx,
  convert Ax.add Cx,
  { ext1 a,
    conv_lhs { rw [eq_add] },
    simp only [pi.add_apply, coe_add, ennreal.add_div],

  }
end

end

end vitali_family
