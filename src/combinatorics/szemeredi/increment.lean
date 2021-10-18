/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .chunk
import .index

/-!
# Increment
-/

universes u v
def sym2_pair_bind {α : Type u} {β : Type v} [decidable_eq β] {s : finset α}
  (f : Π (i : α), i ∈ s → finset β) :
  sym2 {x // x ∈ s} → finset (sym2 β) :=
begin
  refine sym2.lift _,
  refine ⟨λ i j, finset.image quotient.mk ((f _ i.2).product (f _ j.2)), _⟩,
  rintro ⟨i, hi⟩ ⟨j, hj⟩,
  ext k,
  induction k using sym2.induction_on with x y,
  simp only [and_comm (_ ∈ f j _), finset.mem_image, exists_prop, prod.exists, finset.mem_product],
  rw exists_comm,
  apply exists₂_congr,
  intros p q,
  rw sym2.eq_swap,
end

lemma mem_sym2_pair_bind {α β : Type*} [decidable_eq β] {s : finset α}
  (f : Π i ∈ s, finset β) (i₁ i₂ : {x // x ∈ s}) (j₁ j₂ : β) :
  ⟦(j₁, j₂)⟧ ∈ sym2_pair_bind f ⟦(i₁, i₂)⟧ ↔
    (j₁ ∈ f _ i₁.2 ∧ j₂ ∈ f _ i₂.2) ∨ (j₂ ∈ f _ i₁.2 ∧ j₁ ∈ f _ i₂.2) :=
begin
  simp only [sym2_pair_bind, sym2.lift_mk, exists_prop, finset.mem_image, subtype.coe_mk,
    subtype.val_eq_coe, prod.exists, finset.mem_product, sym2.eq_iff],
  split,
  { rintro ⟨_, _, h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩,
    { apply or.inl h },
    { apply or.inr h } },
  tauto {closer := `[simp]},
end

lemma sym2.exists {α : Sort*} {f : sym2 α → Prop} : (∃ (x : sym2 α), f x) ↔ ∃ x y, f ⟦(x, y)⟧ :=
begin
  split,
  { rintro ⟨x, hx⟩,
    induction x using sym2.induction_on with x y,
    exact ⟨x, y, hx⟩ },
  { rintro ⟨x, y, h⟩,
    exact ⟨_, h⟩ }
end

open finset fintype simple_graph
open_locale big_operators classical

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ)

local notation `m` := (card α/exp_bound P.size : ℕ)
local notation `a` := (card α/P.size - m * 4^P.size : ℕ)

/-- The work-horse of SRL. This says that if we have an equipartition which is *not* uniform, then
we can make a (much bigger) equipartition with a slightly higher index. This is helpful since the
index is bounded by a constant (see `index_le_one`), so this process eventually terminates and
yields a not-too-big uniform equipartition. -/
noncomputable def finpartition.is_equipartition.increment : finpartition (univ : finset α) :=
P.bind (λ U, hP.chunk_increment G ε)

open finpartition finpartition.is_equipartition

variables {G ε}

namespace increment

protected lemma size (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε) :
  (hP.increment G ε).size = exp_bound P.size :=
begin
  have hPα' : exp_bound P.size ≤ card α :=
    (nat.mul_le_mul_of_nonneg_left $ nat.pow_le_pow_of_le_left (by norm_num) _).trans hPα,
  have hPpos : 0 < exp_bound P.size := exp_bound_pos.2 (card_pos.2 (nonempty_of_not_uniform hPG)),
  rw [is_equipartition, finset.equitable_on_iff] at hP,
  rw [increment, bind_size],
  simp_rw [finpartition.is_equipartition.chunk_increment, apply_dite finpartition.size],
  rw [sum_dite, sum_const_nat, sum_const_nat, card_attach, card_attach], rotate,
  exact λ x hx, finpartition.equitabilise.size (nat.div_pos hPα' hPpos) _,
  exact λ x hx, finpartition.equitabilise.size (nat.div_pos hPα' hPpos) _,
  rw [nat.sub_add_cancel a_add_one_le_four_pow_size, nat.sub_add_cancel ((nat.le_succ _).trans
    a_add_one_le_four_pow_size), ←add_mul],
  congr,
  rw [filter_card_add_filter_neg_card_eq_card, card_attach, finpartition.size],
end

protected lemma is_equipartition (hP : P.is_equipartition) (G : simple_graph α) (ε : ℝ) :
  (hP.increment G ε).is_equipartition :=
begin
  rw [is_equipartition, set.equitable_on_iff_exists_eq_eq_add_one],
  refine ⟨m, λ A hA, _⟩,
  rw [mem_coe, increment, mem_bind_parts] at hA,
  obtain ⟨U, hU, hA⟩ := hA,
  exact card_eq_of_mem_parts_chunk_increment hA,
end

-- def off_diag : finset (α × α) := (s.product s).filter (λ (a : α × α), a.fst ≠ a.snd)

-- def distinct_pairs (s : finset α) :
--   finset (sym2 α) :=
-- s.off_diag.image quotient.mk


lemma increment_distinct_pairs :
  P.parts.off_diag.attach.bUnion
    (λ UV, (hP.chunk_increment G ε ((mem_off_diag _ _).1 UV.2).1).parts.product
      (hP.chunk_increment G ε ((mem_off_diag _ _).1 UV.2).2.1).parts)
  ⊆ (hP.increment G ε).parts.off_diag :=
begin
  rintro ⟨Ui, Vj⟩,
  simp only [finpartition.is_equipartition.increment, mem_off_diag, bind_parts, mem_bUnion,
    prod.exists, exists_and_distrib_left, exists_prop, mem_product, mem_attach, true_and,
    subtype.exists, and_imp, mem_off_diag, forall_exists_index, bex_imp_distrib, ne.def],
  rintro U V hUV ⟨hUi, hVj⟩,
  simp only [mem_off_diag] at hUV,
  refine ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, _⟩,
  rintro rfl,
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi,
  apply hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (finpartition.le _ hUi hi)
    (finpartition.le _ hVj hi)),
end

-- -- dagger inequality
-- lemma sq_density_sub_eps_le_sum_sq_density_div_card [nonempty α]
-- (hPα : P.size * 16^P.size ≤ card α)
--   (hPε : 100 ≤ 4^P.size * ε^5) (m_pos : 0 < m) (hε₁ : ε ≤ 1)
--   {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} :
--   G.edge_density U V^2 - ε^5/25 ≤
--   (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
--     G.edge_density ab.1 ab.2^2)/16^P.size :=

noncomputable def pair_contrib (G : simple_graph α) (ε : ℝ) (hP : P.is_equipartition)
  (x : {x // x ∈ P.parts.off_diag}) :=
(∑ i in
  (hP.chunk_increment G ε ((mem_off_diag _ _).1 x.2).1).parts.product
    (hP.chunk_increment G ε ((mem_off_diag _ _).1 x.2).2.1).parts,
  G.edge_density i.fst i.snd ^ 2)

lemma off_diag_pairs_le_increment_index :
  ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (hP.increment G ε).size ^ 2 ≤
    (hP.increment G ε).index G :=
begin
  simp_rw [pair_contrib],
  rw ←sum_div,
  refine div_le_div_of_le_of_nonneg _ (sq_nonneg _),
  simp_rw pair_contrib,
  rw ←sum_bUnion,
  { apply sum_le_sum_of_subset_of_nonneg,
    { apply increment_distinct_pairs },
    intros,
    apply sq_nonneg },
  simp only [mem_off_diag, prod.forall, not_and, mem_attach, prod.mk.inj_iff, subtype.mk_eq_mk,
    subtype.forall, ne.def, forall_true_left],
  rintro U₁ U₂ h₁₂ U₃ U₄ h₃₄ h,
  simp only [not_and, prod.mk.inj_iff] at h,
  simp only [mem_off_diag, ne.def] at h₁₂ h₃₄,
  obtain ⟨hU₁, hU₂, h₁₂⟩ := h₁₂,
  obtain ⟨hU₃, hU₄, h₃₄⟩ := h₃₄,
  rintro ⟨Vi, Vj⟩,
  simp only [and_imp, inf_eq_inter, bot_eq_empty, mem_inter, mem_product, not_mem_empty],
  rintro hVi₁ hVj₁ hVi₂ hVj₂,
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hVi₁,
  have := P.disjoint.elim_finset hU₁ hU₃ i (finpartition.le _ hVi₁ hi) (finpartition.le _ hVi₂ hi),
  apply h this,
  obtain ⟨j, hj⟩ := nonempty_of_mem_parts _ hVj₁,
  apply P.disjoint.elim_finset hU₂ hU₄ j (finpartition.le _ hVj₁ hj) (finpartition.le _ hVj₂ hj),
end

example {x : ℝ} : 0 ≤ x^4 :=
begin
  exact pow_bit0_nonneg x 2,
end

-- #exit
lemma pair_contrib_lower_bound [nonempty α] (x : {i // i ∈ P.parts.off_diag}) (hε₁ : ε ≤ 1)
  (hPα : P.size * 16^P.size ≤ card α) (hPε : 100 ≤ 4^P.size * ε^5) :
  G.edge_density x.1.1 x.1.2^2 - ε^5/25 + (if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3) ≤
    pair_contrib G ε hP x / (16^P.size) :=
begin
  split_ifs,
  { rw add_zero,
    apply sq_density_sub_eps_le_sum_sq_density_div_card hPα hPε hε₁ },
  { apply sq_density_sub_eps_le_sum_sq_density_div_card_of_nonuniform hPα hPε hε₁ h }
end

lemma uniform_add_nonuniform_eq_off_diag_pairs [nonempty α] (hε₁ : ε ≤ 1) (hP₇ : 7 ≤ P.size)
  (hPα : P.size * 16^P.size ≤ card α) (hPε : 100 ≤ 4^P.size * ε^5) (hPG : ¬P.is_uniform G ε) :
  (∑ x in P.parts.off_diag, G.edge_density x.1 x.2 ^ 2 + P.size^2 * (ε ^ 5 / 4)) / P.size ^ 2
  ≤ ∑ x in P.parts.off_diag.attach, pair_contrib G ε hP x / (hP.increment G ε).size ^ 2
  :=
begin
  have hP : 1 ≤ P.parts.card := card_pos.2 (parts_nonempty _),
  conv_rhs {
    rw [←sum_div, increment.size _ hPα hPG, exp_bound, ←nat.cast_pow, mul_pow, pow_right_comm,
      nat.cast_mul, mul_comm, ←div_div_eq_div_mul, (show 4^2 = 16, by norm_num), sum_div] },
  rw [←nat.cast_pow, nat.cast_pow 16],
  refine div_le_div_of_le_of_nonneg _ (nat.cast_nonneg _),
  norm_num,
  suffices : ∑ x in P.parts.off_diag, G.edge_density x.1 x.2 ^ 2 + P.size^2 * (ε ^ 5 / 4) ≤
    ∑ x in P.parts.off_diag.attach,
      (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + (if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3)),
  { apply le_trans this,
    apply sum_le_sum,
    intros i hi,
    apply pair_contrib_lower_bound _ i hε₁ hPα hPε },
  have : ∑ x in P.parts.off_diag.attach,
    (G.edge_density x.1.1 x.1.2^2 - ε^5/25 + (if G.is_uniform ε x.1.1 x.1.2 then 0 else ε^4/3)) =
    ∑ x in P.parts.off_diag,
      (G.edge_density x.1 x.2^2 - ε^5/25 + (if G.is_uniform ε x.1 x.2 then 0 else ε^4/3)),
  { convert sum_attach, refl },
  rw [this, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
    zero_add, sum_const, nsmul_eq_mul],
  rw finpartition.is_uniform at hPG,
  rw ←finpartition.non_uniform_pairs,
  simp only [not_le] at hPG,
  apply le_trans _ (add_le_add_left (mul_le_mul_of_nonneg_right hPG.le _) _),
  { conv_rhs { congr, congr, skip, rw [off_diag_card], congr, congr,
      conv { congr, skip, rw ←mul_one P.parts.card }, rw ←nat.mul_sub_left_distrib },
    rw [size_eq_card_parts, mul_assoc, sub_add_eq_add_sub, add_sub_assoc, ←mul_sub_left_distrib,
      mul_div_assoc' ε, ←pow_succ, div_eq_mul_one_div (ε^5), div_eq_mul_one_div (ε^5),
      div_eq_mul_one_div (ε^5), ←mul_sub_left_distrib],
    apply add_le_add_left,
    rw [mul_left_comm, mul_left_comm _ (ε^5)],
    apply mul_le_mul_of_nonneg_left _ (eps_pow_five_pos hPε).le,
    rw [sq, mul_assoc, nat.cast_mul, mul_assoc],
    apply mul_le_mul_of_nonneg_left _ (nat.cast_nonneg _),
    rw [nat.cast_sub hP, mul_sub_right_distrib, nat.cast_one, one_mul, le_sub,
      ←mul_sub_left_distrib],
    rw ←div_le_iff,
    { suffices : (7 : ℝ) ≤ P.parts.card,
      { apply le_trans _ this,
        norm_num },
      exact_mod_cast hP₇ },
    norm_num },
  apply div_nonneg,
  apply pow_bit0_nonneg,
  norm_num,
end

protected lemma index [nonempty α] (hP : P.is_equipartition) (hP₇ : 7 ≤ P.size)
  (hε : 100 < 4^P.size * ε^5) (hPα : P.size * 16^P.size ≤ card α) (hPG : ¬P.is_uniform G ε)
  (hε₁ : ε ≤ 1) :
  P.index G + ε^5 / 4 ≤ (hP.increment G ε).index G :=
begin
  have h := uniform_add_nonuniform_eq_off_diag_pairs hP hε₁ hP₇ hPα hε.le hPG,
  rw [add_div, mul_div_cancel_left] at h,
  exact h.trans (off_diag_pairs_le_increment_index hP),
  norm_num,
  apply ne_of_gt,
  linarith
end

end increment