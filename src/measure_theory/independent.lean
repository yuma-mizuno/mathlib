/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import measure_theory.measure_space
/-!
# Independence of families of measurable sets
-/

open_locale big_operators

universes u v w

namespace measure_theory
variables {α : Type u} [measurable_space α] (ℙ : measure α) [probability_measure ℙ]

/-- A `ι`-indexed family of `ι' i`-indexed families of subsets of α (for `i : ι`) is called
*independent* if for every finite subset `t` of `ι` and every
choice `j i : ι' i` for `i : ι` we have that the measure of the intersections of the sets
`s i (j i)` for `i ∈ t` is the product of the measures. -/
structure independent {ι : Type v} {ι' : ι → Type w} (s : Π (i : ι), ι' i → set α) : Prop :=
--(is_measurable : ∀ (i : ι) (i' : ι' i), is_measurable (s i i'))
(measure_Inter : ∀ (t : finset ι) (j : Π i : ι, ι' i),
  ℙ (⋂ i ∈ t, s i (j i)) = ∏ i in t, ℙ (s i (j i)))

/-- We recover the notion of independent events from independent families by choosing the `s i` to
be one-element sets. -/
def independent_events {ι : Type v} (s : ι → set α) : Prop :=
independent ℙ $ λ i (u : unit), s i

namespace independent
variables {ι : Type v} --{ι' : ι → Type w} {s : Π (i : ι), ι' i → set α}

/-lemma measure_Inter (h : independent μ s) (t : finset ι) (j : Π i : ι, ι' i) :
  μ (⋂ i ∈ t, s i (j i)) = ∏ i in t, μ (s i (j i)) :=
independent.measure_Inter h _ _-/

lemma measure_Inter_events {s : ι → set α} (h : independent_events ℙ s) (t : finset ι) :
  ℙ (⋂ i ∈ t, s i) = ∏ i in t, ℙ (s i) :=
by apply independent.measure_Inter h t (λ i, unit.star)

lemma independent_events_mk {ι : Type v} (s : ι → set α)
  (h : ∀ (t : finset ι), ℙ (⋂ i ∈ t, s i) = ∏ i in t, ℙ (s i)) : independent_events ℙ s :=
{ measure_Inter := λ t j, h t }

attribute [simp] measure_univ

lemma Inter_bool {α : Type*} (f : bool → set α) : (⋂ i, f i) = f ff ∩ f tt :=
by { ext, simp }

lemma bla (s : finset bool) {α : Type*} (f : bool → set α) :
  (⋂ i ∈ s, f i) = (if ff ∈ s then f ff else set.univ) ∩ (if tt ∈ s then f tt else set.univ) :=
begin
  rw Inter_bool,
  ext,
  simp,
  split_ifs; tauto
end

lemma independent_events_bool_iff {s t : set α} : --(hs : is_measurable s) (ht : is_measurable t) :
  (independent_events ℙ (λ i : bool, if i then s else t)) ↔ ℙ (s ∩ t) = ℙ s * ℙ t :=
begin
  split,
  { intro h,
    have := measure_Inter_events ℙ h finset.univ,
    simp only [finset.prod_singleton, finset.prod_insert, finset.mem_univ, if_true,
      bool.coe_sort_ff, bool.coe_sort_tt, if_false, not_false_iff, fintype.univ_bool,
      finset.mem_singleton, set.Inter_pos] at this,
    convert this,
    ext,
    simp only [set.mem_inter_eq, if_true, bool.coe_sort_ff, bool.coe_sort_tt, bool.forall_bool,
      set.mem_Inter, if_false],
    tauto },
  { intro hs,
    apply independent_events_mk,
    apply finset.induction,
    { simp },
    { intros a u ha h,
      rw [finset.prod_insert ha, finset.bInter_insert, ←h, bla],
      split_ifs; cases a;
      try { try { simp only [bool.coe_sort_tt, not_true] at * }, contradiction };
      try { simp [hs] },
      rw [set.inter_comm, mul_comm, hs] } }
end

end independent
end measure_theory
