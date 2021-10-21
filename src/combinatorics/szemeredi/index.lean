/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .mathlib
import combinatorics.choose.bounds
import data.sym.card

/-!
# Index
-/

open_locale big_operators
open finset fintype function relation

variables {α : Type*}

namespace finset
variable [decidable_eq α]

@[simp] lemma off_diag_empty : (∅ : finset α).off_diag = ∅ :=
by rw [off_diag, empty_product, filter_empty]

end finset

/-! ## finpartition.is_uniform -/

variables [decidable_eq α] {s : finset α} (P : finpartition s)
variables (G : simple_graph α) [decidable_rel G.adj]

namespace finpartition
open_locale classical
open finset

noncomputable def non_uniform_pairs (ε : ℝ) :
  finset (finset α × finset α) :=
P.parts.off_diag.filter (λ UV, ¬G.is_uniform ε UV.1 UV.2)

lemma mem_non_uniform_pairs (U V : finset α) (ε : ℝ) :
  (U, V) ∈ P.non_uniform_pairs G ε ↔ U ∈ P.parts ∧ V ∈ P.parts ∧ U ≠ V ∧ ¬G.is_uniform ε U V :=
by rw [non_uniform_pairs, mem_filter, mem_off_diag, and_assoc, and_assoc]

/-- An finpartition is `ε-uniform` iff at most a proportion of `ε` of its pairs of parts are not
`ε-uniform`. -/
def is_uniform (ε : ℝ) : Prop :=
((P.non_uniform_pairs G ε).card : ℝ) ≤ (P.parts.card * (P.parts.card - 1) : ℕ) * ε

lemma empty_is_uniform {P : finpartition s} {G : simple_graph α} {ε : ℝ} (hP : P.parts = ∅) :
  P.is_uniform G ε :=
by simp [is_uniform, hP, non_uniform_pairs]

lemma nonempty_of_not_uniform {P : finpartition s} {G : simple_graph α} {ε : ℝ}
  (h : ¬ P.is_uniform G ε) : P.parts.nonempty :=
nonempty_of_ne_empty (λ h₁, h (empty_is_uniform h₁))

lemma uniform_of_one_le_eps {ε : ℝ} (hε : 1 ≤ ε) :
  P.is_uniform G ε :=
begin
  apply le_trans _ (mul_le_mul_of_nonneg_left hε (nat.cast_nonneg _)),
  rw [mul_one, nat.cast_le],
  apply le_trans (card_filter_le _ _),
  rw [off_diag_card, nat.mul_sub_left_distrib, mul_one],
end

/-- The index is the auxiliary quantity that drives the induction process in the proof of
Szemerédi's Regularity Lemma (see `increment`). As long as we do not have a suitable equipartition,
we will find a new one that has an index greater than the previous one plus some fixed constant.
Then `index_le_one` ensures this process only happens finitely many times. -/
noncomputable def index (P : finpartition s) : ℝ :=
(∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2)/P.parts.card^2

lemma index_nonneg (P : finpartition s) :
  0 ≤ P.index G :=
div_nonneg (finset.sum_nonneg (λ _ _, sq_nonneg _)) (sq_nonneg _)

lemma index_le_one (P : finpartition s) :
  P.index G ≤ 1 :=
begin
  refine div_le_of_nonneg_of_le_mul (sq_nonneg _) zero_le_one _,
  suffices h : ∑ UV in P.parts.off_diag, G.edge_density UV.1 UV.2^2 ≤ P.parts.off_diag.card,
  { apply h.trans,
    rw [off_diag_card, one_mul, ←nat.cast_pow, nat.cast_le, sq],
    apply sub_le_self' },
  refine (sum_le_of_forall_le _ _ 1 _).trans _,
  { intros UV _,
    rw sq_le_one_iff (G.edge_density_nonneg _ _),
    apply G.edge_density_le_one },
  rw nat.smul_one_eq_coe,
end

lemma non_uniform_pairs_discrete {ε : ℝ} (hε : 0 < ε) :
  (finpartition.discrete s).non_uniform_pairs G ε = ∅ :=
begin
  rw eq_empty_iff_forall_not_mem,
  rintro ⟨U, V⟩,
  simp only [finpartition.mem_non_uniform_pairs, finpartition.discrete_parts, mem_map,
    not_and, not_not, embedding.coe_fn_mk, exists_imp_distrib],
  rintro x hx rfl y hy rfl h,
  apply G.is_uniform_singleton hε,
end

lemma discrete_is_uniform {ε : ℝ} (hε : 0 < ε) : (finpartition.discrete s).is_uniform G ε :=
begin
  rw [finpartition.is_uniform, finpartition.card_discrete, non_uniform_pairs_discrete _ hε,
    finset.card_empty, nat.cast_zero],
  apply mul_nonneg (nat.cast_nonneg _) hε.le,
end

end finpartition