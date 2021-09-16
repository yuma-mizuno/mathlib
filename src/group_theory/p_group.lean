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

open fintype mul_action

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

lemma of_card [fintype G] {n : ℕ} (hG : card G = p ^ n) : is_p_group p G :=
λ g, ⟨n, by rw [←hG, pow_card_eq_one]⟩

lemma of_bot : is_p_group p (⊥ : subgroup G) :=
of_card (subgroup.card_bot.trans (pow_zero p).symm)

lemma iff_card [fact p.prime] [fintype G] :
  is_p_group p G ↔ ∃ n : ℕ, card G = p ^ n :=
begin
  have hG : 0 < card G := card_pos_iff.mpr has_one.nonempty,
  refine ⟨λ h, _, λ ⟨n, hn⟩, of_card hn⟩,
  suffices : ∀ q ∈ nat.factors (card G), q = p,
  { use (card G).factors.length,
    rw [←list.prod_repeat, ←list.eq_repeat_of_mem this, nat.prod_factors hG] },
  intros q hq,
  obtain ⟨hq1, hq2⟩ := (nat.mem_factors hG).mp hq,
  haveI : fact q.prime := ⟨hq1⟩,
  obtain ⟨g, hg⟩ := equiv.perm.exists_prime_order_of_dvd_card q hq2,
  obtain ⟨k, hk⟩ := (iff_order_of.mp h) g,
  exact (hq1.pow_eq_iff.mp (hg.symm.trans hk).symm).1.symm,
end

section G_is_p_group

variables (hG : is_p_group p G)

include hG

lemma of_injective {H : Type*} [group H] (ϕ : H →* G) (hϕ : function.injective ϕ) :
  is_p_group p H :=
begin
  simp_rw [is_p_group, ←hϕ.eq_iff, ϕ.map_pow, ϕ.map_one],
  exact λ h, hG (ϕ h),
end

lemma to_subgroup (H : subgroup G) : is_p_group p H :=
hG.of_injective H.subtype subtype.coe_injective

lemma of_surjective {H : Type*} [group H] (ϕ : G →* H) (hϕ : function.surjective ϕ) :
  is_p_group p H :=
begin
  refine λ h, exists.elim (hϕ h) (λ g hg, exists_imp_exists (λ k hk, _) (hG g)),
  rw [←hg, ←ϕ.map_pow, hk, ϕ.map_one],
end

lemma to_quotient (H : subgroup G) [H.normal] :
  is_p_group p (quotient_group.quotient H) :=
hG.of_surjective (quotient_group.mk' H) quotient.surjective_quotient_mk'

lemma of_equiv {H : Type*} [group H] (ϕ : G ≃* H) : is_p_group p H :=
hG.of_surjective ϕ.to_monoid_hom ϕ.surjective

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

variables {α : Type*} [mul_action G α]

lemma card_orbit (a : α) [fintype (orbit G a)] :
  ∃ n : ℕ, card (orbit G a) = p ^ n :=
begin
  let ϕ := orbit_equiv_quotient_stabilizer G a,
  haveI := fintype.of_equiv (orbit G a) ϕ,
  rw [card_congr ϕ, ←subgroup.index_eq_card],
  exact hG.index (stabilizer G a),
end

variables (α) [fintype α] [fintype (fixed_points G α)]

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
lemma nonempty_fixed_point_of_prime_not_dvd_card (hpα : ¬ p ∣ card α) :
  (fixed_points G α).nonempty :=
@set.nonempty_of_nonempty_subtype _ _ begin
rw [←card_pos_iff, pos_iff_ne_zero],
  contrapose! hpα,
  rw [←nat.modeq_zero_iff_dvd, ←hpα],
  exact hG.card_modeq_card_fixed_points α,
end

/-- If a p-group acts on `α` and the cardinality of `α` is a multiple
  of `p`, and the action has one fixed point, then it has another fixed point. -/
lemma exists_fixed_point_of_prime_dvd_card_of_fixed_point
  (hpα : p ∣ card α) {a : α} (ha : a ∈ fixed_points G α) :
  ∃ b, b ∈ fixed_points G α ∧ a ≠ b :=
have hpf : p ∣ card (fixed_points G α) :=
  nat.modeq_zero_iff_dvd.mp ((hG.card_modeq_card_fixed_points α).symm.trans hpα.modeq_zero_nat),
have hα : 1 < card (fixed_points G α) :=
  (fact.out p.prime).one_lt.trans_le (nat.le_of_dvd (card_pos_iff.2 ⟨⟨a, ha⟩⟩) hpf),
let ⟨⟨b, hb⟩, hba⟩ := exists_ne_of_one_lt_card hα ⟨a, ha⟩ in
⟨b, hb, λ hab, hba (by simp_rw [hab])⟩

end G_is_p_group

lemma to_le {H K : subgroup G} (hK : is_p_group p K) (hHK : H ≤ K) : is_p_group p H :=
hK.of_injective (subgroup.inclusion hHK) (λ a b h, subtype.ext (show _, from subtype.ext_iff.mp h))

lemma to_inf_left {H K : subgroup G} (hH : is_p_group p H) : is_p_group p (H ⊓ K : subgroup G) :=
hH.to_le inf_le_left

lemma to_inf_right {H K : subgroup G} (hK : is_p_group p K) : is_p_group p (H ⊓ K : subgroup G) :=
hK.to_le inf_le_right

lemma to_sup_of_normal_right {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  [K.normal] : is_p_group p (H ⊔ K : subgroup G) :=
begin
  intro g,
  obtain ⟨j, hj⟩ := (hH.to_quotient ((H ⊓ K).comap H.subtype)).of_equiv
    (quotient_group.quotient_inf_equiv_prod_normal_quotient H K) g,
  obtain ⟨k, hk⟩ := hK ⟨g ^ (p ^ j), (congr_arg (∈ K) ((H ⊔ K).coe_pow g (p ^ j))).mp
    ((quotient_group.eq_one_iff (g ^ (p ^ j))).mp
      ((quotient_group.coe_pow (K.comap (H ⊔ K).subtype) g (p ^ j)).trans hj))⟩,
  rw [subtype.ext_iff, K.coe_pow, subtype.coe_mk, ←pow_mul, ←pow_add] at hk,
  refine ⟨j + k, by rwa [subtype.ext_iff, (H ⊔ K).coe_pow]⟩,
end

lemma to_sup_of_normal_left {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  [H.normal] : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_of_normal_right hK hH)

lemma to_sup_of_normal_right' {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : H ≤ K.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
let hHK' := to_sup_of_normal_right (hH.of_equiv (subgroup.comap_subtype_equiv_of_le hHK).symm)
  (hK.of_equiv (subgroup.comap_subtype_equiv_of_le subgroup.le_normalizer).symm) in
((congr_arg (λ H : subgroup K.normalizer, is_p_group p H)
  (subgroup.sup_subgroup_of_eq hHK subgroup.le_normalizer)).mp hHK').of_equiv
  (subgroup.comap_subtype_equiv_of_le (sup_le hHK subgroup.le_normalizer))

lemma to_sup_of_normal_left' {H K : subgroup G} (hH : is_p_group p H) (hK : is_p_group p K)
  (hHK : K ≤ H.normalizer) : is_p_group p (H ⊔ K : subgroup G) :=
(congr_arg (λ H : subgroup G, is_p_group p H) sup_comm).mp (to_sup_of_normal_right' hK hH hHK)

end is_p_group

end temp

variables (p : ℕ) (G : Type*) [group G]

def sylow : set (subgroup G) :=
{P | is_p_group p P ∧ ∀ Q : subgroup G, is_p_group p Q → P ≤ Q → Q = P}

variables {p} {G}

/-- A generalization of **Sylow's first theorem**.
  Every `p`-subgroup is contained in a Sylow `p`-subgroup. -/
lemma is_p_group.exists_le_sylow {P : subgroup G} (hP : is_p_group p P) :
  ∃ Q : sylow p G, P ≤ Q :=
begin
  suffices : ∃ (Q : subgroup G) (hQ : is_p_group p Q), P ≤ Q ∧ ∀ R : subgroup G,
    is_p_group p R → Q ≤ R → R = Q,
  { obtain ⟨Q, hQ1, hQ2, hQ3⟩ := this,
    exact ⟨⟨Q, hQ1, hQ3⟩, hQ2⟩ },
  refine zorn.zorn_nonempty_partial_order₀ {Q | is_p_group p Q} (λ c hc1 hc2 Q hQ, _) P hP,
  let R : subgroup G :=
  { carrier := ⋃ (R : c), R,
    one_mem' := ⟨Q, ⟨⟨Q, hQ⟩, rfl⟩, Q.one_mem⟩,
    inv_mem' := λ g ⟨_, ⟨R, rfl⟩, hg⟩, ⟨R, ⟨R, rfl⟩, R.1.inv_mem hg⟩,
    mul_mem' := λ g h ⟨_, ⟨R, rfl⟩, hg⟩ ⟨_, ⟨S, rfl⟩, hh⟩, (hc2.total_of_refl R.2 S.2).elim
      (λ T, ⟨S, ⟨S, rfl⟩, S.1.mul_mem (T hg) hh⟩) (λ T, ⟨R, ⟨R, rfl⟩, R.1.mul_mem hg (T hh)⟩) },
  exact ⟨R, λ ⟨g, _, ⟨S, rfl⟩, hg⟩, by
  { refine exists_imp_exists (λ k hk, subtype.ext _) (hc1 S.2 ⟨g, hg⟩),
    exact (R.coe_pow _ _).trans ((S.1.coe_pow _ _).symm.trans (subtype.ext_iff.mp hk)) },
  λ M hM g hg, ⟨M, ⟨⟨M, hM⟩, rfl⟩, hg⟩⟩,
end

instance sylow_nonempty : nonempty (sylow p G) :=
nonempty_of_exists is_p_group.of_bot.exists_le_sylow

--note: maybe there's a way to avoid fintype.of_injective, so that this can be made computable
/-noncomputable instance [fintype G] : fintype (sylow p G) :=
@subtype.fintype _ _ (λ _, classical.prop_decidable _)
  (fintype.of_injective subgroup.carrier (λ _ _ h, subgroup.ext (set.ext_iff.mp h)))-/

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

instance : mul_action G (sylow p G) :=
{ smul := λ g P, ⟨g • P, sorry⟩,
  one_smul := sorry,
  mul_smul := sorry }

--mem_smul lemma

lemma subgroup.sylow_mem_fixed_points_iff
  (H : subgroup G) {P : sylow p G} :
  P ∈ mul_action.fixed_points H (sylow p G) ↔ H ≤ P.1.normalizer :=
begin
  refine ⟨λ h g hg k, _, λ h g, _⟩,
  have key := h ⟨g, hg⟩,
  sorry,
  have key := h g.2,
  refine subtype.ext (subgroup.ext (λ k, _)),
  sorry
end

lemma is_p_group.inf_normalizer_sylow {P : subgroup G} (hP : is_p_group p P) (Q : sylow p G) :
  P ⊓ Q.1.normalizer = P ⊓ Q :=
le_antisymm (le_inf inf_le_left (sup_eq_right.mp (Q.2.2 (P ⊓ Q.1.normalizer ⊔ Q)
  (hP.to_inf_left.to_sup_of_normal_right' Q.2.1 inf_le_right) le_sup_right)))
  (inf_le_inf_left P subgroup.le_normalizer)

lemma is_p_group.sylow_mem_fixed_points_iff
  {P : subgroup G} (hP : is_p_group p P) {Q : sylow p G} :
  Q ∈ mul_action.fixed_points P (sylow p G) ↔ P ≤ Q :=
by rw [P.sylow_mem_fixed_points_iff, ←inf_eq_left, hP.inf_normalizer_sylow, inf_eq_left]

variables (p) (G)

/-- A generalization of **Sylow's second theorem**.
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate. -/
lemma sylow_conjugate [hp : fact p.prime] [fintype (sylow p G)] (P Q : sylow p G) :
  ∃ g : G, g • P = Q :=
begin
  classical,
  have key := λ {R : sylow p G} {S : mul_action.orbit G P},
  calc S ∈ mul_action.fixed_points R (mul_action.orbit G P)
      ↔ S.1 ∈ mul_action.fixed_points R (sylow p G) : forall_congr (λ a, subtype.ext_iff)
  ... ↔ R ≤ S : R.2.1.sylow_mem_fixed_points_iff
  ... ↔ S.1 = R : ⟨λ h, subtype.ext (R.2.2 S S.1.2.1 h), ge_of_eq⟩,
  suffices : set.nonempty (mul_action.fixed_points Q (mul_action.orbit G P)),
  { exact exists.elim this (λ R hR, (congr_arg _ (key.mp hR)).mp R.2) },
  apply Q.2.1.nonempty_fixed_point_of_prime_not_dvd_card,
  refine λ h, hp.out.not_dvd_one (nat.modeq_zero_iff_dvd.mp _),
  calc 1 = fintype.card (mul_action.fixed_points P (mul_action.orbit G P)) : _
    ... ≡ fintype.card (mul_action.orbit G P) [MOD p] :
      (P.2.1.card_modeq_card_fixed_points (mul_action.orbit G P)).symm
    ... ≡ 0 [MOD p] : nat.modeq_zero_iff_dvd.mpr h,
  convert (set.card_singleton (⟨P, mul_action.mem_orbit_self P⟩ : mul_action.orbit G P)).symm,
  exact set.eq_singleton_iff_unique_mem.mpr ⟨key.mpr rfl, λ R hR, subtype.ext (key.mp hR)⟩,
end

/-- A generalization of **Sylow's third theorem**.
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`. -/
lemma card_sylow_modeq_one [fact p.prime] [fintype (sylow p G)] :
  fintype.card (sylow p G) ≡ 1 [MOD p] :=
begin
  refine sylow_nonempty.elim (λ P : sylow p G, _),
  have key : mul_action.fixed_points P (sylow p G) = {P} :=
  set.ext (λ Q, calc Q ∈ mul_action.fixed_points P (sylow p G)
      ↔ P ≤ Q : P.2.1.sylow_mem_fixed_points_iff
  ... ↔ Q = P : ⟨λ h, subtype.ext (P.2.2 Q Q.2.1 h), ge_of_eq⟩
  ... ↔ Q ∈ {P} : set.mem_singleton_iff.symm),
  haveI : fintype (mul_action.fixed_points P (sylow p G)) :=
  by { rw key, exact set.fintype_singleton P },
  calc fintype.card (sylow p G) ≡ fintype.card (mul_action.fixed_points P (sylow p G)) [MOD p] :
    P.2.1.card_modeq_card_fixed_points (sylow p G)
  ... = 1 : by simp_rw key; convert set.card_singleton P,
end
