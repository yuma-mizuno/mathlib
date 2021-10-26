/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.interval

/-!
# Intervals of multisets as finsets

This file provides the `locally_finite_order` instance for `multiset α`.
-/

open finset
open_locale big_operators

lemma multiset.card_powerset_to_finset {α : Type*} [decidable_eq α] (s : multiset α) :
  s.powerset.to_finset.card = ∏ x in s.to_finset, (s.count x + 1) :=
sorry

variables {α : Type*}

namespace multiset
variables [decidable_eq α] (s t : multiset α)

instance {α : Type*} [decidable_eq α] : decidable_rel ((⊆) : multiset α → multiset α → Prop) :=
λ s t, multiset.decidable_forall_multiset

instance {α : Type*} [decidable_eq α] : decidable_rel ((≤) : multiset α → multiset α → Prop) :=
λ s t, multiset.decidable_forall_multiset

instance {α : Type*} [decidable_eq α] : decidable_rel ((<) : multiset α → multiset α → Prop) :=
λ s t, multiset.decidable_forall_multiset

-- If we had `multiset.ssubsets` (akin to `finset.ssubsets`), we could provide `Ico` and `Ioo` more
-- cleanly.
instance : locally_finite_order (multiset α) :=
{ finset_Ioc := λ s t, t.powerset.to_finset.filter ((<) s),
  finset_mem_Ioc := λ s t u,
    by {rw [finset.mem_filter, mem_to_finset, mem_powerset], exact and_comm _ _ },
  ..locally_finite_order.of_Icc (multiset α)
    (λ s t, t.powerset.to_finset.filter ((≤) s))
    (λ s t u, by { rw [finset.mem_filter, mem_to_finset, mem_powerset], exact and_comm _ _ }) }

lemma Icc_eq_filter_powerset : finset.Icc s t = t.powerset.to_finset.filter ((≤) s) := rfl

lemma Ioc_eq_filter_powerset : finset.Ioc s t = t.powerset.to_finset.filter ((<) s) := rfl

lemma Iic_eq_powerset : finset.Iic s = s.powerset.to_finset := filter_true_of_mem $ λ t _, bot_le

variables {s t}

lemma Icc_eq_image_powerset (h : s ≤ t) :
  finset.Icc s t = (t - s).powerset.to_finset.image ((+) s) :=
begin
  ext u,
  simp_rw [finset.mem_Icc, finset.mem_image, exists_prop, mem_to_finset, mem_powerset],
  split,
  { rintro ⟨hs, ht⟩,
    exact ⟨u - s, tsub_le_tsub_right ht _, add_tsub_cancel_of_le hs⟩ },
  { rintro ⟨v, hv, rfl⟩,
    exact ⟨le_add_right _ _, add_le_of_le_tsub_left_of_le h hv⟩ }
end

/-- Cardinality of a non-empty `Icc` of finsets. -/
lemma card_Icc_finset (h : s ⊆ t) : (Icc s t).card = 2 ^ (t.card - s.card) :=
begin
  rw [←card_sdiff h, ←card_powerset, Icc_eq_image_powerset h, finset.card_image_eq_iff_inj_on],
  rintro u hu v hv (huv : s ⊔ u = s ⊔ v),
  rw [mem_coe, mem_powerset] at hu hv,
  rw [←(disjoint_sdiff.mono_right hu : disjoint s u).sup_sdiff_cancel_left,
    ←(disjoint_sdiff.mono_right hv : disjoint s v).sup_sdiff_cancel_left, huv],
end

/-- Cardinality of an `Ico` of finsets. -/
lemma card_Ico_finset (h : s ⊆ t) : (Ico s t).card = 2 ^ (t.card - s.card) - 1 :=
by rw [card_Ico_eq_card_Icc_sub_one (le_iff_subset.2 h), card_Icc_finset h]

/-- Cardinality of an `Ioc` of finsets. -/
lemma card_Ioc_finset (h : s ⊆ t) : (Ioc s t).card = 2 ^ (t.card - s.card) - 1 :=
by rw [card_Ioc_eq_card_Icc_sub_one (le_iff_subset.2 h), card_Icc_finset h]

/-- Cardinality of an `Ioo` of finsets. -/
lemma card_Ioo_finset (h : s ⊆ t) : (Ioo s t).card = 2 ^ (t.card - s.card) - 2 :=
by rw [card_Ioo_eq_card_Icc_sub_two (le_iff_subset.2 h), card_Icc_finset h]


end multiset
