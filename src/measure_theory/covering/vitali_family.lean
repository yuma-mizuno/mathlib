/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.metric_space.basic
import measure_theory.measure.regular

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

This file defines Vitali families and proves its basic properties.
-/

open measure_theory metric set filter topological_space
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

variables {m : measurable_space α} {μ : measure α}
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

noncomputable instance [second_countable_topology α] : encodable h.t :=
h.t_countable.to_encodable

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
  calc ρ s ≤ ∑' (x : h.t), ρ (h.u x) : h.measure_le_tsum_of_absolutely_continuous hρ
  ... ≤ ∑' (x : h.t), ν (h.u x) : ennreal.tsum_le_tsum (λ x, (h.u_mem_f x.2).1)
  ... = ν (⋃ (x : h.t), h.u x) :
    by rw [measure_Union h.u_disjoint_subtype (λ i, (h.is_closed_u i.2).measurable_set)]
  ... ≤ ν U : measure_mono (Union_subset (λ i, (h.u_mem_f i.2).2))
  ... ≤ ν s + ε : νU
end

/-- If a measure `ρ` is singular with respect to `μ`, then for `μ` almost every `x`, the ratio
`ρ a / μ a` tends to zero when `a` shrinks to `x` along the Vitali family. This makes sense
as `μ a` is eventually positive by `ae_eventually_measure_pos`. -/
lemma ae_eventually_measure_zero_of_singular [sigma_compact_space α] [borel_space α]
  {ρ : measure α} (hρ : ρ ⊥ₘ μ) [is_locally_finite_measure ρ] [is_locally_finite_measure μ] :
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
      simp only [measure.coe_nnreal_smul, algebra.mul_smul_comm, pi.smul_apply],
      simp only [has_scalar.smul, has_scalar.comp.smul, ennreal.coe_of_nnreal_hom, ← mul_assoc],
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

/-- A set of points `s` satisfying both `ρ a ≤ c * μ a` and `ρ a ≥ d * μ a` at arbitrarily small
sets in a Vitali family has measure `0` if `c < d`. Indeed, the first inequality should imply
that `ρ s ≤ c * μ s`, and the second one that `ρ s ≥ d * μ s`, a contradiction if `0 < μ s`. -/
theorem null_of_frequently_le_of_frequently_ge [sigma_compact_space α] [borel_space α]
  {ρ : measure α} [is_locally_finite_measure ρ] [is_locally_finite_measure μ]
  (hρ : ρ ≪ μ) {c d : ℝ≥0} (hcd : c < d) (s : set α)
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
    apply (ennreal.mul_lt_mul_right _ _).2 (ennreal.coe_lt_coe.2 hcd),
    { assume h', exact h h' },
    { exact (lt_of_le_of_lt (measure_mono (inter_subset_right _ _)) μo).ne },
  end
  ... ≤ ρ s' : v.measure_le_of_frequently_le ρ
    ((measure.absolutely_continuous.refl μ).smul d) s' (λ x hx, hd x hx.1)
end

end vitali_family
