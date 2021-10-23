/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import .bounds
import .finpartitions
import .prereqs
import .witness

/-!
# Chunk of `increment`
-/

open finpartition finset fintype relation
open_locale big_operators classical

variables {α : Type*} [fintype α] {P : finpartition (univ : finset α)} (hP : P.is_equipartition)
  (G : simple_graph α) (ε : ℝ) {U : finset α} (hU : U ∈ P.parts) (V : finset α)

local notation `m` := (card α/exp_bound P.parts.card : ℕ)
local notation `a` := (card α/P.parts.card - m * 4^P.parts.card : ℕ)

/-- The witnesses of non uniformity among the parts of a finpartition. -/
noncomputable def finpartition.witnesses
  (P : finpartition (univ : finset α)) (G : simple_graph α) (ε : ℝ) (U : finset α) :=
(P.parts.filter (λ V, U ≠ V ∧ ¬G.is_uniform ε U V)).image (G.witness ε U)

/-- The portion of `increment` that partitions `U`. -/
noncomputable def finpartition.is_equipartition.chunk_increment :
  finpartition U :=
dite (U.card = m * 4^P.parts.card + a)
  (λ hUcard, (atomise U (P.witnesses G ε U)).equitabilise $ card_aux₂ hUcard)
  (λ hUcard, (atomise U (P.witnesses G ε U)).equitabilise $ card_aux₃ hP hU hUcard)
  -- hP and hU are used to get that U has size m * 4^P.parts.card + a or m * 4^P.parts.card + a + 1

/-- The portion of `chunk_increment` that's contained in the witness of non uniformity of `U` and
`V`. -/
noncomputable def finpartition.is_equipartition.star (V : finset α) : finset (finset α) :=
(hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ G.witness ε U V)

/-! # star -/

/-- Each thing in star is a subset of the witness -/
lemma subset_witness_of_mem_star : ∀ A ∈ hP.star G ε hU V, A ⊆ G.witness ε U V :=
λ A hA, (mem_filter.1 hA).2

lemma bUnion_star_subset_witness : (hP.star G ε hU V).bUnion id ⊆ G.witness ε U V :=
bUnion_subset_iff_forall_subset.2 (subset_witness_of_mem_star hP G ε hU V)

variables {hP G ε hU V}

lemma star_subset_chunk_increment : hP.star G ε hU V ⊆ (hP.chunk_increment G ε hU).parts :=
filter_subset _ _

lemma star_pairwise_disjoint : (hP.star G ε hU V : set (finset α)).pairwise_disjoint :=
(hP.chunk_increment G ε hU).disjoint.subset star_subset_chunk_increment

lemma witness_sdiff_bUnion_star_small (hV : V ∈ P.parts) (hUV : U ≠ V) (h₂ : ¬G.is_uniform ε U V) :
  (G.witness ε U V \ (hP.star G ε hU V).bUnion id).card ≤ 2^(P.parts.card - 1) * m :=
begin
  have hX : G.witness ε U V ∈ P.witnesses G ε U := mem_image_of_mem _ (by simp [hUV, hV, h₂]),
  have q : G.witness ε U V \ (hP.star G ε hU V).bUnion id ⊆
    ((atomise U (P.witnesses G ε U)).parts.filter
      (λ B, B ⊆ G.witness ε U V ∧ B.nonempty)).bUnion
      (λ B, B \ ((hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ B)).bUnion id),
  { intros x hx,
    rw [←union_of_atoms' (G.witness ε U V) hX (G.witness_subset h₂),
      finpartition.is_equipartition.star, mem_sdiff, mem_bUnion] at hx,
    simp only [not_exists, mem_bUnion, and_imp, filter_congr_decidable, exists_prop, mem_filter,
      not_and, mem_sdiff, id.def, mem_sdiff] at hx ⊢,
    obtain ⟨⟨B, hB₁, hB₂⟩, hx⟩ := hx,
    exact ⟨B, hB₁, hB₂, λ A hA AB, hx A hA $ AB.trans hB₁.2.1⟩ },
  apply (card_le_of_subset q).trans (card_bUnion_le.trans _),
  have :
    ∑ i in (atomise U (P.witnesses G ε U)).parts.filter (λ B, B ⊆ G.witness ε U V ∧ B.nonempty), m
      ≤ 2 ^ (P.parts.card - 1) * m,
  { rw sum_const_nat,
    { apply nat.mul_le_mul_right,
      have t := partial_atomise (G.witness ε U V) hX,
      rw filter_congr_decidable at t,
      apply t.trans (pow_le_pow (by norm_num) (nat.sub_le_sub_right _ _)),
      apply card_image_le.trans (card_le_of_subset (filter_subset _ _)) },
    { intros,
      refl } },
  apply le_trans _ this,
  have : ∀ B ∈ (atomise U (P.witnesses G ε U)).parts,
          (B \ ((hP.chunk_increment G ε hU).parts.filter (λ x, x ⊆ B)).bUnion id).card ≤ m,
  { intros B hB,
    rw [finpartition.is_equipartition.chunk_increment],
    split_ifs with h₁,
    { convert almost_in_atoms_of_mem_parts_equitabilise (card_aux₂ h₁) hB },
    convert almost_in_atoms_of_mem_parts_equitabilise (card_aux₃ hP hU h₁) hB },
  apply sum_le_sum (λ B hB, this B (filter_subset _ _ hB)),
end

lemma one_sub_eps_mul_card_witness_le_card_star (hV : V ∈ P.parts) (hUV : U ≠ V)
  (hunif : ¬G.is_uniform ε U V) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) :
  (1 - ε/10) * (G.witness ε U V).card ≤ ((hP.star G ε hU V).bUnion id).card :=
begin
  have hP₁ : 0 < P.parts.card := finset.card_pos.2 ⟨_, hU⟩,
  have : (2^P.parts.card : ℝ) * m/(U.card * ε) ≤ ε/10,
  { rw [←div_div_eq_div_mul, div_le_iff' (eps_pos hPε)],
    refine le_of_mul_le_mul_left _ (pow_pos zero_lt_two P.parts.card),
    calc
      2^P.parts.card * ((2^P.parts.card * m : ℝ)/U.card)
          = (2 * 2)^P.parts.card * m/U.card : by rw [mul_pow, ←mul_div_assoc, mul_assoc]
      ... = 4^P.parts.card * m/U.card : by norm_num
      ... ≤ 1 : div_le_one_of_le (pow_mul_m_le_card_part hP hU) (nat.cast_nonneg _)
      ... ≤ 2^P.parts.card * ε^2 / 10 : begin
              refine (one_le_sq_iff (div_nonneg (mul_nonneg (pow_nonneg (@zero_le_two ℝ _) _) $
                sq_nonneg _) $ by norm_num)).1 _,
              rw [div_pow, mul_pow, pow_right_comm, ←pow_mul ε,
                one_le_div (sq_pos_of_ne_zero (10 : ℝ) $ by norm_num)],
              calc
                (10 ^ 2 : ℝ)
                = 100 : by norm_num
                ... ≤ 4^P.parts.card * ε^5 : hPε
                ... ≤ 4^P.parts.card * ε^4
                    : mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (eps_pos hPε).le hε₁
                        (nat.le_succ _)) (pow_nonneg zero_lt_four.le _)
                ... = (2^2)^P.parts.card * ε ^ (2 * 2) : by norm_num,
            end
      ... = 2^P.parts.card * (ε * (ε / 10)) : by rw [mul_div_assoc, sq, mul_div_assoc] },
  calc
    (1 - ε/10) * (G.witness ε U V).card
        ≤ (1 - 2^P.parts.card * m/(U.card * ε)) * (G.witness ε U V).card
        : mul_le_mul_of_nonneg_right (sub_le_sub_left this _) (nat.cast_nonneg _)
    ... = (G.witness ε U V).card - 2^P.parts.card * m/(U.card * ε) * (G.witness ε U V).card
        : by rw [sub_mul, one_mul]
    ... ≤ (G.witness ε U V).card - 2^(P.parts.card - 1) * m : begin
          refine sub_le_sub_left _ _,
          have : (2 : ℝ)^P.parts.card = 2^(P.parts.card - 1) * 2,
          { rw [←pow_succ', nat.sub_add_cancel hP₁] },
          rw [←mul_div_right_comm, this, mul_right_comm _ (2 : ℝ), mul_assoc, le_div_iff
            (mul_pos (nat.cast_pos.2 (P.nonempty_of_mem_parts hU).card_pos) (eps_pos hPε))],
          refine mul_le_mul_of_nonneg_left _ _,
          exact (G.witness_card hunif).trans
            (le_mul_of_one_le_left (nat.cast_nonneg _) one_le_two),
          exact mul_nonneg (pow_nonneg zero_le_two _) (nat.cast_nonneg _),
        end
    ... ≤ ((hP.star G ε hU V).bUnion id).card
        : begin
          norm_cast,
          rw [sub_le, ←nat.cast_sub (finset.card_le_of_subset $ bUnion_star_subset_witness
            hP G ε hU V), ←card_sdiff (bUnion_star_subset_witness hP G ε hU V), nat.cast_le],
          exact witness_sdiff_bUnion_star_small hV hUV hunif,
        end
end

variables {hP G ε U hU V}

/-! # chunk_increment -/

lemma card_chunk_increment (m_pos : 0 < m) :
  (hP.chunk_increment G ε hU).parts.card = 4^P.parts.card :=
begin
  rw finpartition.is_equipartition.chunk_increment,
  split_ifs,
  { rw [finpartition.equitabilise.parts_card m_pos, nat.sub_add_cancel],
    exact le_of_lt a_add_one_le_four_pow_parts_card },
  { rw [finpartition.equitabilise.parts_card m_pos, nat.sub_add_cancel],
    exact a_add_one_le_four_pow_parts_card }
end

lemma card_eq_of_mem_parts_chunk_increment {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  A.card = m ∨ A.card = m + 1 :=
begin
  simp [finpartition.is_equipartition.chunk_increment] at hA,
  by_cases hUcard : U.card = m * 4^P.parts.card + a,
  { rw dif_pos hUcard at hA,
    exact finpartition.card_eq_of_mem_parts_equitabilise _ hA },
  rw dif_neg hUcard at hA,
  exact finpartition.card_eq_of_mem_parts_equitabilise _ hA,
end

lemma m_le_card_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  (m : ℝ) ≤ A.card :=
begin
  obtain h | h := card_eq_of_mem_parts_chunk_increment hA; rw h,
  exact nat.cast_le.2 (nat.le_succ _),
end

lemma card_le_m_add_one_of_mem_chunk_increment_parts {A : finset α}
  (hA : A ∈ (hP.chunk_increment G ε hU).parts) :
  A.card ≤ m + 1 :=
begin
  obtain h | h := card_eq_of_mem_parts_chunk_increment hA; rw h,
  exact nat.le_succ _,
end

lemma card_bUnion_star_le_m_add_one_card_star_mul :
  ((hP.star G ε hU V).bUnion id).card ≤ (hP.star G ε hU V).card * (m + 1) :=
card_bUnion_le_card_mul _ _ _ $ λ s hs,
  card_le_m_add_one_of_mem_chunk_increment_parts $ star_subset_chunk_increment hs

lemma le_sum_card_subset_chunk_increment_parts (m_pos : (0 : ℝ) < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (A.card : ℝ) * u.card ≤ (∑ V in A, V.card)/(m/(m + 1)) :=
begin
  rw le_div_iff, swap,
  { exact div_pos m_pos (nat.cast_add_one_pos _) },
  calc
    (A.card : ℝ) * u.card * (m/(m + 1))
        = A.card * m * (u.card/(m + 1))
        : by rw [←mul_div_assoc, mul_right_comm, mul_div_assoc]
    ... ≤ A.card * m
        : mul_le_of_le_one_right (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _))
          ((div_le_one $ by exact nat.cast_add_one_pos _).2 $ nat.cast_le.2 $
          card_le_m_add_one_of_mem_chunk_increment_parts $ hA hu)
    ... = ∑ V in A, (m : ℝ)
        : by rw [sum_const, nsmul_eq_mul]
    ... ≤ ∑ V in A, V.card
        : sum_le_sum (λ V hV, m_le_card_of_mem_chunk_increment_parts $ hA hV)
end

lemma sum_card_subset_chunk_increment_parts_le (m_pos : (0 : ℝ) < m) {A : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) {u : finset α} (hu : u ∈ A) :
  (∑ V in A, (V.card : ℝ))/((m + 1)/m) ≤ A.card * u.card :=
(div_le_iff (div_pos (@nat.cast_add_one_pos ℝ _ _ _) m_pos)).2 (calc
  ∑ V in A, (V.card : ℝ)
      ≤ ∑ V in A, (m + 1)
      : sum_le_sum (λ V hV, nat.cast_le.2 $
        card_le_m_add_one_of_mem_chunk_increment_parts $ hA hV)
  ... = A.card * (m + 1) : by rw [sum_const, nsmul_eq_mul]
  ... ≤ A.card * (m + 1) * (u.card/m) : le_mul_of_one_le_right (mul_nonneg (nat.cast_nonneg _)
        (nat.cast_add_one_pos _).le) ((one_le_div m_pos).2
        (m_le_card_of_mem_chunk_increment_parts $ hA hu))
  ... = A.card * u.card * ((m + 1)/m)
      : by rw [←mul_div_assoc, mul_right_comm, mul_div_assoc])

lemma one_sub_le_m_div_m_add_one_sq [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) :
  1 - ε^5/50 ≤ (m/(m + 1))^2 :=
begin
  calc
    1 - ε^5/50
        = 1 - 2/(100/ε^5) : begin
          rw [div_div_eq_mul_div, mul_comm, mul_div_assoc, div_eq_mul_one_div],
          norm_num,
         end
    ... ≤ 1 - 2/m : sub_le_sub_left (div_le_div_of_le_left zero_le_two
          (div_pos (by norm_num) (eps_pow_five_pos hPε)) (hundred_div_ε_pow_five_le_m hPα hPε)) _
    ... ≤ 1 - 2/(m + 1) : sub_le_sub_left (div_le_div_of_le_left zero_le_two
          (nat.cast_pos.2 (m_pos hPα)) ((le_add_iff_nonneg_right _).2 zero_le_one)) _
    ... ≤ 1 - 2/(m + 1) + 1/(m + 1)^2
        : le_add_of_nonneg_right (div_nonneg zero_le_one (sq_nonneg _))
    ... = ((m + 1 - 1)/(m + 1))^2 : by rw [sub_div, div_self (nat.cast_add_one_ne_zero m :
            (m : ℝ) + 1 ≠ 0), sub_sq, div_pow, one_pow, mul_one, mul_one_div]
    ... = (m/(m + 1))^2 : by rw add_sub_cancel,
end

lemma m_add_one_div_m_le_one_add [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) :
  ((m + 1 : ℝ)/m)^2 ≤ 1 + ε^5/49 :=
begin
  rw ←one_add_div (m_coe_pos hPα).ne',
  have : 1 + 1/(m:ℝ) ≤ 1 + ε^5/100,
  { apply add_le_add_left,
    rw ←one_div_div (100:ℝ),
    refine one_div_le_one_div_of_le (div_pos (by norm_num) (eps_pow_five_pos hPε)) _,
    apply hundred_div_ε_pow_five_le_m hPα hPε },
  apply (pow_le_pow_of_le_left _ this 2).trans,
  { generalize h : ε^5 = i,
    have hi' : 0 ≤ i,
    { rw ←h,
      apply (eps_pow_five_pos hPε).le },
    have hi : i ≤ 1,
    { rw ←h,
      apply pow_le_one _ (eps_pos hPε).le hε₁ },
    rw [add_sq, one_pow, div_pow, mul_one, add_assoc, mul_div_comm],
    apply add_le_add_left,
    rw [←le_sub_iff_add_le', div_eq_mul_one_div i, ←mul_sub_left_distrib],
    norm_num,
    nlinarith [hi, hi'] },
  exact add_nonneg (by norm_num) (one_div_nonneg.2 (nat.cast_nonneg _)),
end

lemma density_sub_eps_le_sum_density_div_card [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
  G.edge_density (A.bUnion id) (B.bUnion id) - ε^5/50 ≤
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) :=
calc
  G.edge_density (A.bUnion id) (B.bUnion id) - ε^5/50
      ≤ (1 - ε^5/50) * G.edge_density (A.bUnion id) (B.bUnion id)
      : begin
          rw [sub_mul, one_mul],
          exact sub_le_sub_left (mul_le_of_le_one_right
            (div_nonneg (eps_pow_five_pos hPε).le $ by norm_num) $ G.edge_density_le_one _ _) _,
        end
  ... ≤ (m/(m + 1))^2 * G.edge_density (A.bUnion id) (B.bUnion id)
      : mul_le_mul_of_nonneg_right (one_sub_le_m_div_m_add_one_sq hPα hPε)
        (G.edge_density_nonneg _ _)
  ... = pairs_count G.adj (A.bUnion id) (B.bUnion id) /
        ((A.bUnion id).card/(m/(m + 1)) * ((B.bUnion id).card/(m/(m + 1))))
      : begin
          unfold simple_graph.edge_density pairs_density,
          simp_rw [←div_div_eq_div_mul],
          rw [div_div_eq_mul_div, div_div_eq_mul_div],
          ring,
        end
  ... = ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/((∑ aa in A, (aa.card : ℝ))/(m/(m + 1))
        * ((∑ b in B, (b.card : ℝ))/(m/(m + 1))))
      : begin
          rw [←sup_eq_bUnion, ←sup_eq_bUnion,
            relation.pairs_count_finpartition (of_subset _ hA rfl) (of_subset _ hB rfl),
            ←(of_subset _ hA rfl).sum_card_parts, ←(of_subset _ hB rfl).sum_card_parts],
          simp only [nat.cast_sum],
          rw [sum_div, of_subset_parts, of_subset_parts],
        end
  ... ≤ ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/(A.card * ab.1.card *
        (B.card * ab.2.card))
        : begin
          refine sum_le_sum (λ x hx, div_le_div_of_le_left (nat.cast_nonneg _) _ _);
          rw mem_product at hx,
          { norm_cast,
            refine mul_pos (mul_pos _ _) (mul_pos _ _); rw finset.card_pos,
            exacts [⟨x.1, hx.1⟩, nonempty_of_mem_parts _ (hA hx.1), ⟨x.2, hx.2⟩,
              nonempty_of_mem_parts _ (hB hx.2)] },
          refine mul_le_mul (le_sum_card_subset_chunk_increment_parts (m_coe_pos hPα) hA hx.1)
            (le_sum_card_subset_chunk_increment_parts (m_coe_pos hPα) hB hx.2) _
            (div_nonneg _ (div_nonneg _ _));
          norm_cast; exact nat.zero_le _,
        end
  ... = (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card)
      : begin
          unfold simple_graph.edge_density pairs_density,
          rw sum_div,
          simp_rw div_div_eq_div_mul,
          refine finset.sum_congr rfl (λ x _, _),
          rw [mul_comm (B.card : ℝ), ←mul_assoc, ←mul_assoc, mul_comm _ (A.card : ℝ), ←mul_assoc],
        end

lemma sum_density_div_card_le_density_add_eps [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
  (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) ≤
  G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49 :=
begin
  have m_add_one_div_m_pos : (0 : ℝ) < (m + 1)/m :=
    div_pos (nat.cast_add_one_pos _) (m_coe_pos hPα),
  calc
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card)
        = ∑ ab in A.product B,
          pairs_count G.adj ab.1 ab.2/(A.card * ab.1.card * (B.card * ab.2.card))
        : begin
            unfold simple_graph.edge_density pairs_density,
            rw sum_div,
            simp_rw div_div_eq_div_mul,
            refine finset.sum_congr rfl (λ x _, _),
            rw [mul_comm (B.card : ℝ), ←mul_assoc, ←mul_assoc, mul_comm _ (A.card : ℝ), ←mul_assoc],
          end
    ... ≤ ∑ ab in A.product B, pairs_count G.adj ab.1 ab.2/((∑ aa in A, (aa.card : ℝ))/((m + 1)/m)
          * ((∑ b in B, (b.card : ℝ))/((m + 1)/m)))
        : begin
            refine sum_le_sum (λ x hx, div_le_div_of_le_left (nat.cast_nonneg _) _ _);
            rw mem_product at hx,
            { refine mul_pos (div_pos _ m_add_one_div_m_pos)
                (div_pos _ m_add_one_div_m_pos); norm_cast,
              { exact (finpartition.nonempty_of_mem_parts _ $
                hA hx.1).card_pos.trans_le (single_le_sum (λ _ _, nat.zero_le _) hx.1) },
              { refine (finpartition.nonempty_of_mem_parts _ $
                hB hx.2).card_pos.trans_le (single_le_sum (λ _ _, nat.zero_le _) hx.2) } },
            refine mul_le_mul (sum_card_subset_chunk_increment_parts_le (m_coe_pos hPα) hA hx.1)
              (sum_card_subset_chunk_increment_parts_le (m_coe_pos hPα) hB hx.2)
              (div_nonneg _ (div_nonneg _ _)) _; norm_cast; exact nat.zero_le _,
          end
    ... = pairs_count G.adj (A.bUnion id) (B.bUnion id) /
          ((A.bUnion id).card/((m + 1)/m) * ((B.bUnion id).card/((m + 1)/m)))
        : begin
            rw [←sup_eq_bUnion, ←sup_eq_bUnion,
              relation.pairs_count_finpartition (of_subset _ hA rfl) (of_subset _ hB rfl),
              ←(of_subset _ hA rfl).sum_card_parts, ←(of_subset _ hB rfl).sum_card_parts],
            simp only [nat.cast_sum],
            rw [eq_comm, sum_div, of_subset_parts, of_subset_parts],
          end
    ... = ((m + 1)/m)^2 * G.edge_density (A.bUnion id) (B.bUnion id)
        : begin
            unfold simple_graph.edge_density pairs_density,
            simp only [←div_div_eq_div_mul],
            rw [div_div_eq_mul_div, div_div_eq_mul_div],
            ring,
          end
    ... ≤ (1 + ε^5/49) * G.edge_density (A.bUnion id) (B.bUnion id)
        : mul_le_mul_of_nonneg_right (m_add_one_div_m_le_one_add hPα hPε hε₁)
          (G.edge_density_nonneg _ _)
    ... ≤ G.edge_density (A.bUnion id) (B.bUnion id) + ε^5/49
        : begin
            rw [add_mul, one_mul],
            exact add_le_add_left (mul_le_of_le_one_right (div_nonneg (eps_pow_five_pos hPε).le
              (by norm_num)) (G.edge_density_le_one _ _)) _,
          end,
end

lemma average_density_near_total_density [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} {A B : finset (finset α)}
  (hA : A ⊆ (hP.chunk_increment G ε hU).parts) (hB : B ⊆ (hP.chunk_increment G ε hV).parts) :
|(∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) -
  G.edge_density (A.bUnion id) (B.bUnion id)| ≤ ε^5/49 :=
begin
  rw abs_sub_le_iff,
  split,
  { rw sub_le_iff_le_add',
    apply sum_density_div_card_le_density_add_eps hPα hPε hε₁ hA hB },
  suffices : G.edge_density (A.bUnion id) (B.bUnion id) -
    (∑ ab in A.product B, G.edge_density ab.1 ab.2)/(A.card * B.card) ≤ ε^5/50,
  { apply this.trans,
    exact div_le_div_of_le_left (eps_pow_five_pos hPε).le (by norm_num) (by norm_num) },
  rw sub_le_iff_le_add,
  rw ←sub_le_iff_le_add',
  apply density_sub_eps_le_sum_density_div_card hPα hPε hA hB,
end

-- predagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card_aux [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
  G.edge_density U V^2 - ε^5/25 ≤
  ((∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2)/16^P.parts.card)^2 :=
begin
  obtain hGε | hGε := le_total (G.edge_density U V) (ε^5/50),
  { calc
      G.edge_density U V^2 - ε^5/25
          ≤ G.edge_density U V - ε^5/25
          : sub_le_sub_right (sq_le (G.edge_density_nonneg _ _) (G.edge_density_le_one _ _)) _
      ... ≤ ε^5/50 - ε^5/25
          : sub_le_sub_right hGε _
      ... ≤ 0
          : sub_nonpos_of_le (div_le_div_of_le_left (eps_pow_five_pos hPε).le (by norm_num)
              (by norm_num))
      ... ≤ _ : sq_nonneg _ },
  rw ←sub_nonneg at hGε,
  calc
    G.edge_density U V^2 - ε^5/25
        ≤ G.edge_density U V^2 - ε^5/25 * G.edge_density U V
        : sub_le_sub_left (mul_le_of_le_one_right
            (div_nonneg (eps_pow_five_pos hPε).le $ by norm_num) $ G.edge_density_le_one _ _) _
    ... ≤ G.edge_density U V^2 - ε^5/25 * G.edge_density U V + (ε^5/50)^2
        : le_add_of_nonneg_right (sq_nonneg _)
    ... = (G.edge_density U V - ε^5/50)^2
        : by { rw [sub_sq, mul_right_comm, mul_div_comm, div_eq_mul_inv], norm_num }
    ... = (G.edge_density ((hP.chunk_increment G ε hU).parts.bUnion id)
            ((hP.chunk_increment G ε hV).parts.bUnion id) - ε^5/50)^2
        : by rw [finpartition.bUnion_parts, finpartition.bUnion_parts]
    ... ≤ ((∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
            G.edge_density ab.1 ab.2)/((hP.chunk_increment G ε hU).parts.card
            * (hP.chunk_increment G ε hV).parts.card))^2
        : pow_le_pow_of_le_left
            (by rwa [finpartition.bUnion_parts, finpartition.bUnion_parts])
            (density_sub_eps_le_sum_density_div_card hPα hPε set.subset.rfl set.subset.rfl) 2
    ... ≤ ((∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2)/16^P.parts.card)^2
        : begin
            rw [card_chunk_increment (m_pos hPα), card_chunk_increment (m_pos hPα), ←nat.cast_mul,
              ←mul_pow],
            norm_cast,
          end,
end

-- dagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5)
  {U V : finset α} (hU : U ∈ P.parts) (hV : V ∈ P.parts) :
  G.edge_density U V^2 - ε^5/25 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.parts.card :=
begin
  apply (sq_density_sub_eps_le_sum_sq_density_div_card_aux hPα hPε hU hV).trans,
  convert chebyshev _ _;
  rw [card_product, nat.cast_mul, card_chunk_increment (m_pos hPα),
    card_chunk_increment (m_pos hPα), ←nat.cast_mul, ←mul_pow];
  norm_cast,
end

lemma abs_density_star_sub_density_le_eps (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (hUV' : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  |G.edge_density ((hP.star G ε hU V).bUnion id) ((hP.star G ε hV U).bUnion id) -
    G.edge_density (G.witness ε U V) (G.witness ε V U)| ≤ ε/5 :=
begin
  convert lemma_A G.adj
    (bUnion_star_subset_witness hP G ε hU V)
    (bUnion_star_subset_witness hP G ε hV U)
    (div_nonneg (eps_pos hPε).le $ by norm_num)
    (one_sub_eps_mul_card_witness_le_card_star hV hUV' hUV hPε hε₁)
    (one_sub_eps_mul_card_witness_le_card_star hU hUV'.symm (λ hVU, hUV hVU.symm) hPε hε₁),
  rw [mul_div_comm, div_eq_mul_one_div],
  norm_num,
end

lemma m_bound {x : ℝ} (hx : 0 < x) : (x + 1) * (1 - 1/x) / x ≤ 1 :=
begin
  rw [div_le_one hx, one_sub_div hx.ne', mul_div_assoc', div_le_iff hx],
  linarith,
end

lemma eps_le_card_star_div [nonempty α] (hPα : P.parts.card * 16^P.parts.card ≤ card α)
  (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1) {U V : finset α} (hU : U ∈ P.parts)
  (hV : V ∈ P.parts) (hUV : U ≠ V) (hunif : ¬ G.is_uniform ε U V) :
  4/5 * ε ≤ (hP.star G ε hU V).card / 4^P.parts.card :=
begin
  have hm : (0 : ℝ) ≤ 1 - 1/m :=
    sub_nonneg_of_le (one_div_le_one_of_one_le $ one_le_m_coe hPα),
  have hε : 0 ≤ 1 - ε / 10 :=
    sub_nonneg_of_le (div_le_one_of_le (hε₁.trans $ by norm_num) $ by norm_num),
  calc
    4/5 * ε
        = (1 - 1/10) * (1 - 1/9) * ε : by norm_num
    ... ≤ (1 - ε/10) * (1 - 1/m) * ((G.witness ε U V).card / U.card)
        : mul_le_mul
            (mul_le_mul (sub_le_sub_left (div_le_div_of_le_of_nonneg hε₁ $ by norm_num) _)
              (sub_le_sub_left (div_le_div_of_le_left zero_le_one (by norm_num)
                (by exact_mod_cast ((show 9 ≤ 100, by norm_num).trans
                $ hundred_le_m hPα hPε hε₁))) _)
              (by norm_num) hε)
            ((le_div_iff' $ (@nat.cast_pos ℝ _ _ _).2 (P.nonempty_of_mem_parts hU).card_pos).2
              (G.witness_card hunif))
            (eps_pos hPε).le
            (mul_nonneg hε hm)
    ... = (1 - ε/10) * (G.witness ε U V).card * ((1 - 1/m) / U.card)
        : by rw [mul_assoc, mul_assoc, mul_div_comm]
    ... ≤ ((hP.star G ε hU V).bUnion id).card * ((1 - 1/m) / U.card)
        : (mul_le_mul_of_nonneg_right
            (one_sub_eps_mul_card_witness_le_card_star hV hUV hunif hPε hε₁)
            (div_nonneg hm $ nat.cast_nonneg _))
    ... ≤ (hP.star G ε hU V).card * (m + 1) * ((1 - 1/m) / U.card) :
          begin
            norm_cast,
            exact mul_le_mul_of_nonneg_right (nat.cast_le.2
              card_bUnion_star_le_m_add_one_card_star_mul) (div_nonneg hm $ nat.cast_nonneg _),
          end
    ... ≤ (hP.star G ε hU V).card * (m + 1) * ((1 - 1/m) / (4^P.parts.card * m))
        : mul_le_mul_of_nonneg_left (div_le_div_of_le_left hm
            (mul_pos four_pow_pos $ m_coe_pos hPα) $ pow_mul_m_le_card_part hP hU)
            (mul_nonneg (nat.cast_nonneg _) $ add_nonneg (nat.cast_nonneg _) zero_le_one)
    ... ≤ (hP.star G ε hU V).card / 4^P.parts.card :
    begin
      rw [mul_assoc, mul_comm ((4:ℝ)^P.parts.card), ←div_div_eq_div_mul, ←mul_div_assoc,
        ←div_mul_eq_mul_div_comm],
      refine mul_le_of_le_one_right (div_nonneg (nat.cast_nonneg _) four_pow_pos.le) _,
      rw mul_div_assoc',
      apply m_bound,
      rw nat.cast_pos,
      apply m_pos hPα,
    end
end

lemma stuff [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (h_diff : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  3/4 * ε ≤
    |(∑ ab in (hP.star G ε hU V).product (hP.star G ε hV U), G.edge_density ab.1 ab.2)
      / ((hP.star G ε hU V).card * (hP.star G ε hV U).card) -
        (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2)/16^P.parts.card| :=
begin
  rw [(show (16:ℝ) = 4^2, by norm_num), pow_right_comm, sq ((4:ℝ)^_)],
  set p := (∑ ab in (hP.star G ε hU V).product (hP.star G ε hV U), G.edge_density ab.1 ab.2)
      / ((hP.star G ε hU V).card * (hP.star G ε hV U).card),
  set q := (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2)/(4 ^ P.parts.card * 4 ^ P.parts.card),
  change _ ≤ |p - q|,
  set r := G.edge_density ((hP.star G ε hU V).bUnion id) ((hP.star G ε hV U).bUnion id),
  set s := G.edge_density (G.witness ε U V) (G.witness ε V U),
  set t := G.edge_density U V,
  have hrs : |r - s| ≤ ε/5 := abs_density_star_sub_density_le_eps hPε hε₁ h_diff hUV,
  have hst : ε ≤ |s - t| := G.witness_pair_spec h_diff hUV,
  have hpr : |p - r| ≤ ε^5/49 := average_density_near_total_density hPα hPε hε₁
    star_subset_chunk_increment star_subset_chunk_increment,
  have hqt : |q - t| ≤ ε^5/49,
  { have := average_density_near_total_density hPα hPε hε₁
      (subset.refl (hP.chunk_increment G ε hU).parts)
      (subset.refl (hP.chunk_increment G ε hV).parts),
    have m_pos : 0 < m := m_pos hPα,
    simp_rw [←sup_eq_bUnion, sup_parts, card_chunk_increment m_pos, nat.cast_pow] at this,
    norm_num at this,
    exact this },
  have hε : 0 < ε := eps_pos hPε,
  have hpr' : |p - r| ≤ ε/49,
  { refine hpr.trans (div_le_div_of_le_of_nonneg _ (by norm_num)),
    simpa using pow_le_pow_of_le_one hε.le hε₁ (show 1 ≤ 5, by norm_num) },
  have hqt' : |q - t| ≤ ε/49,
  { apply hqt.trans (div_le_div_of_le_of_nonneg _ (by norm_num)),
    simpa using pow_le_pow_of_le_one hε.le hε₁ (show 1 ≤ 5, by norm_num) },
  rw abs_sub_le_iff at hrs hpr' hqt',
  rw le_abs at hst ⊢,
  cases hst,
  left, linarith,
  right, linarith,
end

lemma product_subset_product {α β : Type*} {A A' : finset α} {B B' : finset β}
  (hA : A' ⊆ A) (hB : B' ⊆ B) :
  A'.product B' ⊆ A.product B :=
begin
  rintro ⟨x,y⟩ h,
  simp only [mem_product] at h ⊢,
  exact ⟨hA h.1, hB h.2⟩,
end

-- double dagger inequality
lemma sq_density_sub_eps_le_sum_sq_density_div_card_of_nonuniform [nonempty α]
  (hPα : P.parts.card * 16^P.parts.card ≤ card α) (hPε : 100 ≤ 4^P.parts.card * ε^5) (hε₁ : ε ≤ 1)
  {U V : finset α} {hU : U ∈ P.parts} {hV : V ∈ P.parts} (h_diff : U ≠ V)
  (hUV : ¬ G.is_uniform ε U V) :
  G.edge_density U V^2 - ε^5/25 + ε^4/3 ≤
  (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
    G.edge_density ab.1 ab.2^2)/16^P.parts.card :=
calc
  G.edge_density U V^2 - ε^5/25 + ε^4/3
      ≤ G.edge_density U V^2 - ε^5/25 +
          (hP.star G ε hU V).card * (hP.star G ε hV U).card/16^P.parts.card * (9/16) * ε^2 :
        begin
          apply add_le_add_left,
          have Ul : 4/5 * ε ≤ (hP.star G ε hU V).card / _ :=
            eps_le_card_star_div hPα hPε hε₁ hU hV h_diff hUV,
          have Vl : 4/5 * ε ≤ (hP.star G ε hV U).card / _ :=
            eps_le_card_star_div hPα hPε hε₁ hV hU h_diff.symm (λ h, hUV h.symm),
          rw [(show (16:ℝ) = 4^2, by norm_num), pow_right_comm, sq ((4:ℝ)^_), ←div_mul_div,
            mul_assoc],
          have UVl :=
            mul_le_mul Ul Vl
              (mul_nonneg (by norm_num) (eps_pos hPε).le)
              (div_nonneg (nat.cast_nonneg _) four_pow_pos.le),
          apply le_trans _ (mul_le_mul_of_nonneg_right UVl _),
          { field_simp,
            ring_nf,
            apply mul_le_mul_of_nonneg_right,
            norm_num,
            apply pow_nonneg (eps_pos hPε).le },
          { norm_num,
            apply pow_nonneg (eps_pos hPε).le },
        end
  ... ≤ (∑ ab in (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts,
          G.edge_density ab.1 ab.2^2)/16^P.parts.card :
    begin
      -- have := product_subset_product,
      have t : (hP.star G ε hU V).product (hP.star G ε hV U) ⊆
        (hP.chunk_increment G ε hU).parts.product (hP.chunk_increment G ε hV).parts :=
          product_subset_product star_subset_chunk_increment star_subset_chunk_increment,
      have hε : 0 ≤ ε := (eps_pos hPε).le,
      have h₁ : 0 ≤ 3/4 * ε := by linarith,
      have := lemma_B_ineq t (λ x, G.edge_density x.1 x.2) (G.edge_density U V^2 - ε^5/25) h₁ _ _,
      { simp_rw [card_product, card_chunk_increment (m_pos hPα), ←mul_pow, nat.cast_pow, mul_pow,
          div_pow, ←mul_assoc] at this,
        norm_num at this,
        exact this },
      { simp_rw [card_product, card_chunk_increment (m_pos hPα), ←mul_pow],
        norm_num,
        apply stuff hPα hPε hε₁ h_diff hUV },
      { rw card_product,
        apply (sq_density_sub_eps_le_sum_sq_density_div_card_aux hPα hPε hU hV).trans,
        rw [card_chunk_increment (m_pos hPα), card_chunk_increment (m_pos hPα), ←mul_pow],
        norm_num,
        apply hP }
    end