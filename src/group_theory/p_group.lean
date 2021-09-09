/-
Copyright (c) 2018 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Thomas Browning
-/

import group_theory.index
import group_theory.perm.cycle_type
import group_theory.quotient_group

/-!
# p-groups

This file contains a proof that if `G` is a `p`-group acting on a finite set `α`,
then the number of fixed points of the action is congruent mod `p` to the cardinality of `α`.
It also contains proofs of some corollaries of this lemma about existence of fixed points.
-/

section temp

open_locale big_operators

variables (p : ℕ) (G : Type*) [group G]

/-- A p-group is a group in which every element has prime power order -/
def is_p_group : Prop := ∀ g : G, ∃ k : ℕ, g ^ (p ^ k) = 1

variables {p} {G}

namespace is_p_group

lemma iff_order_of [hp : fact p.prime] :
  is_p_group p G ↔ ∀ g : G, ∃ k : ℕ, order_of g = p ^ k :=
forall_congr (λ g, ⟨λ ⟨k, hk⟩, exists_imp_exists (by exact λ j, Exists.snd)
  ((nat.dvd_prime_pow hp.out).mp (order_of_dvd_of_pow_eq_one hk)),
  exists_imp_exists (λ k hk, by rw [←hk, pow_order_of_eq_one])⟩)

lemma of_card [fintype G] {n : ℕ} (hG : fintype.card G = p ^ n) : is_p_group p G :=
λ g, ⟨n, by rw [←hG, pow_card_eq_one]⟩

lemma of_bot : is_p_group p (⊥ : subgroup G) :=
of_card (show fintype.card (⊥ : subgroup G) = p ^ 0, from subgroup.card_bot)

lemma iff_card [fact p.prime] [fintype G] :
  is_p_group p G ↔ ∃ n : ℕ, fintype.card G = p ^ n :=
begin
  have hG : 0 < fintype.card G := fintype.card_pos_iff.mpr has_one.nonempty,
  refine ⟨λ h, _, λ ⟨n, hn⟩, of_card hn⟩,
  suffices : ∀ q ∈ nat.factors (fintype.card G), q = p,
  { use (fintype.card G).factors.length,
    rw [←list.prod_repeat, ←list.eq_repeat_of_mem this, nat.prod_factors hG] },
  intros q hq,
  obtain ⟨hq1, hq2⟩ := (nat.mem_factors hG).mp hq,
  haveI : fact q.prime := ⟨hq1⟩,
  obtain ⟨g, hg⟩ := equiv.perm.exists_prime_order_of_dvd_card q hq2,
  obtain ⟨k, hk⟩ := (iff_order_of.mp h) g,
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm,
end

lemma to_le {H K : subgroup G} (hK : is_p_group p K) (hHK : H ≤ K) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow] at hK ⊢,
  exact λ h, hK ⟨h, hHK h.2⟩,
end

lemma to_inf_left {H K : subgroup G} (hH : is_p_group p H) : is_p_group p (H ⊓ K : subgroup G) :=
hH.to_le inf_le_left

lemma to_inf_right {H K : subgroup G} (hK : is_p_group p K) : is_p_group p (H ⊓ K : subgroup G) :=
hK.to_le inf_le_right

lemma to_sup_right {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : K ≤ H.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_left hK hH hHK)

section p_group

variables (hG : is_p_group p G)

include hG

lemma to_subgroup (H : subgroup G) : is_p_group p H :=
begin
  simp_rw [is_p_group, subtype.ext_iff, subgroup.coe_pow],
  exact λ h, hG h,
end

lemma to_quotient (H : subgroup G) [H.normal] :
  is_p_group p (quotient_group.quotient H) :=
begin
  refine quotient.ind' (forall_imp (λ g, _) hG),
  exact exists_imp_exists (λ k h, (quotient_group.coe_pow H g _).symm.trans (congr_arg coe h)),
end

variables [hp : fact p.prime]

include hp

lemma index (H : subgroup G) [fintype (quotient_group.quotient H)] :
  ∃ n : ℕ, H.index = p ^ n :=
begin
  obtain ⟨n, hn⟩ := iff_card.mp (hG.to_quotient H.normal_core),
  obtain ⟨k, hk1, hk2⟩ := (nat.dvd_prime_pow hp.out).mp ((congr_arg _
    (H.normal_core.index_eq_card.trans hn)).mp (subgroup.index_dvd_of_le H.normal_core_le)),
  exact ⟨k, hk2⟩,
end

lemma card_orbit {α : Type*} [mul_action G α] (a : α) [fintype (mul_action.orbit G a)] :
  ∃ n : ℕ, fintype.card (mul_action.orbit G a) = p ^ n :=
begin
  let ϕ := mul_action.orbit_equiv_quotient_stabilizer G a,
  haveI := fintype.of_equiv (mul_action.orbit G a) ϕ,
  rw [fintype.card_congr ϕ, ←subgroup.index_eq_card],
  exact index hG (mul_action.stabilizer G a),
end

end p_group

lemma to_sup_left {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : H ≤ K.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
begin
  replace hHK : H ⊔ K ≤ K.normalizer := sup_le hHK subgroup.le_normalizer,
  let N := K.comap (H ⊔ K).subtype,
  haveI : N.normal := begin
    -- opposite of le_normalizer_of_normal ?
    sorry
  end,
  let Q := quotient_group.quotient N,
  have key : is_p_group p Q,
  { -- ? generalize this isomorphism theorem to the case where `H ⊔ K ≤ K.normalizer`
    have key := quotient_group.quotient_inf_equiv_prod_normal_quotient, },
  -- K is a normal subgroup of H ⊔ K
  -- quotient by K
  -- iso theorem!
  -- etc...
  sorry
end

end is_p_group

namespace mul_action

open fintype

variables (α : Type*) [mul_action G α] [fintype α] [fintype (fixed_points G α)]
  (hG : is_p_group p G) [fact p.prime]

include hG

/-- If `G` is a `p`-group acting on a finite set `α`, then the number of fixed points
  of the action is congruent mod `p` to the cardinality of `α` -/
lemma card_modeq_card_fixed_points : card α ≡ card (fixed_points G α) [MOD p] :=
begin
  classical,
  calc card α = card (Σ y : quotient (orbit_rel G α), {x // quotient.mk' x = y}) :
    card_congr (equiv.sigma_preimage_equiv (@quotient.mk' _ (orbit_rel G α))).symm
  ... = ∑ a : quotient (orbit_rel G α), card {x // quotient.mk' x = a} : card_sigma _
  ... ≡ ∑ a : fixed_points G α, 1 [MOD p] : _
  ... = _ : by simp; refl,
  rw [←zmod.eq_iff_modeq_nat p, nat.cast_sum, nat.cast_sum],
  have key : ∀ x, card {y // (quotient.mk' y : quotient (orbit_rel G α)) = quotient.mk' x} =
    card (orbit G x) := λ x, by simp only [quotient.eq']; congr,
  refine eq.symm (finset.sum_bij_ne_zero (λ a _ _, quotient.mk' a.1) (λ _ _ _, finset.mem_univ _)
    (λ a₁ a₂ _ _ _ _ h, subtype.eq ((mem_fixed_points' α).mp a₂.2 a₁.1 (quotient.exact' h)))
      (λ b, quotient.induction_on' b (λ b _ hb, _)) (λ a ha _, by
      { rw [key, mem_fixed_points_iff_card_orbit_eq_one.mp a.2] })),
  obtain ⟨k, hk⟩ := hG.card_orbit b,
  have : k = 0 := nat.le_zero_iff.1 (nat.le_of_lt_succ (lt_of_not_ge (mt (pow_dvd_pow p)
    (by rwa [pow_one, ←hk, ←nat.modeq_zero_iff_dvd, ←zmod.eq_iff_modeq_nat, ←key])))),
  exact ⟨⟨b, mem_fixed_points_iff_card_orbit_eq_one.2 $ by rw [hk, this, pow_zero]⟩,
    finset.mem_univ _, (ne_of_eq_of_ne nat.cast_one one_ne_zero), rfl⟩,
end

/-- If a p-group acts on `α` and the cardinality of `α` is not a multiple
  of `p` then the action has a fixed point. -/
lemma nonempty_fixed_point_of_prime_not_dvd_card (hp : ¬ p ∣ card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
rw [←card_pos_iff, pos_iff_ne_zero],
  contrapose! hp,
  rw [←nat.modeq_zero_iff_dvd, ←hp],
  exact card_modeq_card_fixed_points α hG,
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (hpα : p ∣ card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ card (fixed_points G α) :=
  nat.modeq_zero_iff_dvd.mp ((card_modeq_card_fixed_points α hG).symm.trans hpα.modeq_zero_nat),
have hα : 1 < card (fixed_points G α) :=
  (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba (by simp_rw [hab])⟩

end mul_action

end temp

variables (p : ℕ) (G : Type*) [group G]

def sylow : set (subgroup G) :=
{H | is_p_group p H ∧ ∀ K : subgroup G, is_p_group p K → H ≤ K → K = H}

variables {p} {G}

lemma is_p_group.exists_le_sylow {H : subgroup G} (hH : is_p_group p H) :
  ∃ K : sylow p G, H ≤ K :=
begin
  suffices : ∃ (K : subgroup G) (hK : is_p_group p K), H ≤ K ∧ ∀ L : subgroup G,
    is_p_group p L → K ≤ L → L = K,
  { obtain ⟨K, hK1, hK2, hK3⟩ := this,
    exact ⟨⟨K, hK1, hK3⟩, hK2⟩ },
  refine zorn.zorn_nonempty_partial_order₀ {K | is_p_group p K} (λ c hc1 hc2 K hK, _) H hH,
  let L : subgroup G :=
  { carrier := ⋃ (Q : c), Q,
    one_mem' := ⟨K, ⟨⟨K, hK⟩, rfl⟩, K.one_mem⟩,
    inv_mem' := λ g ⟨_, ⟨L, rfl⟩, hg⟩, ⟨L, ⟨L, rfl⟩, L.1.inv_mem hg⟩,
    mul_mem' := λ g h ⟨_, ⟨L, rfl⟩, hg⟩ ⟨_, ⟨M, rfl⟩, hh⟩, (hc2.total_of_refl L.2 M.2).elim
      (λ H, ⟨M, ⟨M, rfl⟩, M.1.mul_mem (H hg) hh⟩) (λ H, ⟨L, ⟨L, rfl⟩, L.1.mul_mem hg (H hh)⟩) },
  exact ⟨L, λ ⟨g, _, ⟨M, rfl⟩, hg⟩, by
  { refine exists_imp_exists (λ k hk, subtype.ext _) (hc1 M.2 ⟨g, hg⟩),
    exact (L.coe_pow _ _).trans ((M.1.coe_pow _ _).symm.trans (subtype.ext_iff.mp hk)) },
  λ M hM g hg, ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩,
end

instance sylow_nonempty : nonempty (sylow p G) :=
nonempty_of_exists is_p_group.of_bot.exists_le_sylow

--note: fintype.of_injective makes this noncomputable, so might as well use classical
noncomputable instance [fintype G] : fintype (sylow p G) :=
@subtype.fintype _ _ (λ _, classical.prop_decidable _)
  (fintype.of_injective subgroup.carrier (λ _ _ h, subgroup.ext (set.ext_iff.mp h)))

instance mul_action' : mul_action G (subgroup G) :=
{ smul := λ g H, H.comap (mul_aut.conj g)⁻¹.to_monoid_hom,
  one_smul := λ H, by
  { change H.comap (mul_aut.conj (1 : G))⁻¹.to_monoid_hom = H,
    rw mul_aut.conj.map_one,
    ext,
    refl },
  mul_smul := λ g h H, by
  { change H.comap (mul_aut.conj (g * h))⁻¹.to_monoid_hom = _,
    rw mul_aut.conj.map_mul,
    refl } }

-- is_p_group preserved under smul
-- mem_sylow preserved under smul

instance (H : subgroup G) : mul_action H (sylow p G) :=
{ smul := λ g K, ⟨g • K, sorry⟩,
  one_smul := sorry,
  mul_smul := sorry }

--mem_smul lemma

lemma subgroup.sylow_mem_fixed_points_iff
  (H : subgroup G) {K : sylow p G} :
  K ∈ mul_action.fixed_points H (sylow p G) ↔ H ≤ K.1.normalizer :=
begin
  refine ⟨λ h g hg k, _, λ h g, _⟩,
  have key := h ⟨g, hg⟩,
  sorry,
  have key := h g.2,
  refine subtype.ext (subgroup.ext (λ k, _)),
  sorry
end

lemma is_p_group_inf_normalizer_sylow {H : subgroup G} (hH : is_p_group p H) (K : sylow p G) :
  H ⊓ K.1.normalizer = H ⊓ K :=
le_antisymm (le_inf inf_le_left (sup_eq_right.mp (K.2.2 (H ⊓ K.1.normalizer ⊔ K)
  (hH.to_inf_left.to_sup_left K.2.1 inf_le_right) le_sup_right)))
  (inf_le_inf_left H subgroup.le_normalizer)

lemma is_p_group.sylow_mem_fixed_points_iff
  {H : subgroup G} (hH : is_p_group p H) {K : sylow p G} :
  K ∈ mul_action.fixed_points H (sylow p G) ↔ H ≤ K :=
by rw [H.sylow_mem_fixed_points_iff, ←inf_eq_left, is_p_group_inf_normalizer_sylow hH, inf_eq_left]

variables (p) (G)

lemma card_sylow_modeq_one [fact p.prime] [fintype (sylow p G)] :
  fintype.card (sylow p G) ≡ 1 [MOD p] :=
begin
  refine sylow_nonempty.elim (λ H : sylow p G, _),
  have key : mul_action.fixed_points H.1 (sylow p G) = {H} :=
  set.eq_singleton_iff_unique_mem.mpr ⟨H.2.1.sylow_mem_fixed_points_iff.mpr le_rfl,
    λ K hK, subtype.ext (H.2.2 K K.2.1 (H.2.1.sylow_mem_fixed_points_iff.mp hK))⟩,
  haveI : fintype (mul_action.fixed_points H.1 (sylow p G)) :=
  by { rw key, exact set.fintype_singleton H },
  calc fintype.card (sylow p G) ≡ fintype.card (mul_action.fixed_points H.1 (sylow p G)) [MOD p] :
    mul_action.card_modeq_card_fixed_points (sylow p G) H.2.1
  ... = 1 : by simp_rw key; convert set.card_singleton H,
end
