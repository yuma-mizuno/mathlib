/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/

import group_theory.p_group

/-!
# Sylow theorems

The Sylow theorems are the following results for every finite group `G` and every prime number `p`.

* There exists a Sylow `p`-subgroup of `G`.
* All Sylow `p`-subgroups of `G` are conjugate to each other.
* Let `nₚ` be the number of Sylow `p`-subgroups of `G`, then `nₚ` divides the index of the Sylow
  `p`-subgroup, `nₚ ≡ 1 [MOD p]`, and `nₚ` is equal to the index of the normalizer of the Sylow
  `p`-subgroup in `G`.

In this file, currently only the first of these results is proven.

## Main statements

* `exists_subgroup_card_pow_prime`: A generalisation of Sylow's first theorem:
  For every prime power `pⁿ` dividing `G`, there exists a subgroup of `G` of order `pⁿ`.
* `is_p_group.exists_le_sylow`: A generalisation of Sylow's first theorem:
  Every `p`-subgroup is contained in a Sylow `p`-subgroup.
* `sylow_conjugate`: A generalization of Sylow's second theorem:
  If the number of Sylow `p`-subgroups is finite, then all Sylow `p`-subgroups are conjugate.
* `card_sylow_modeq_one`: A generalization of Sylow's third theorem:
  If the number of Sylow `p`-subgroups is finite, then it is congruent to `1` modulo `p`.
-/

section infinite_sylow

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

def aux : mul_aut G →* function.End (sylow p G) :=
{ to_fun := λ ϕ P, ⟨P.1.comap ϕ⁻¹.to_monoid_hom, by
  { refine ⟨λ g, _, λ Q hQ hPQ, _⟩,
    { refine exists_imp_exists (λ k hk, _) (P.2.1 ⟨ϕ⁻¹.to_monoid_hom g, g.2⟩),
      rw [subtype.ext_iff, subgroup.coe_pow] at hk ⊢,
      exact (ϕ⁻¹.map_eq_one_iff).mp ((monoid_hom.map_pow _ _ _).trans hk) },
    { have key := P.2.2 (Q.comap ϕ.to_monoid_hom),
      sorry } }⟩,
  map_one' := funext (λ P, subtype.ext (subgroup.ext (λ g, iff.rfl))),
  map_mul' := λ ϕ ψ, funext (λ P, subtype.ext (by
  { change P.1.comap _ = (P.1.comap _).comap _,
    rw [subgroup.comap_comap, mul_inv_rev],
    refl })) }

instance : mul_action G (sylow p G) :=
mul_action.of_End_hom (aux.comp mul_aut.conj)

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

-- orbit eq top

-- stablizer eq normalizer

variables {p} {G}

noncomputable def sylow_equiv_quotient_normalizer [fintype (sylow p G)] (P : sylow p G) :
  sylow p G ≃ quotient_group.quotient P.1.normalizer :=
calc sylow p G ≃ mul_action.orbit G P : sorry
... ≃ quotient_group.quotient (mul_action.stabilizer G P) :
  mul_action.orbit_equiv_quotient_stabilizer G P
... ≃ quotient_group.quotient P.1.normalizer : sorry

noncomputable instance [fintype (sylow p G)] (P : sylow p G) :
  fintype (quotient_group.quotient P.1.normalizer) :=
fintype.of_equiv (sylow p G) (sylow_equiv_quotient_normalizer P)

lemma card_sylow_eq_card_quotient_normalizer [fintype (sylow p G)] (P : sylow p G) :
  fintype.card (sylow p G) = fintype.card (quotient_group.quotient P.1.normalizer) :=
fintype.card_congr (sylow_equiv_quotient_normalizer P)

lemma card_sylow_eq_index_normalizer [fintype (sylow p G)] (P : sylow p G) :
  fintype.card (sylow p G) = P.1.normalizer.index :=
(card_sylow_eq_card_quotient_normalizer P).trans P.1.normalizer.index_eq_card.symm

end infinite_sylow

section finite_sylow

variables {p : ℕ} {G : Type*} [group G]

-- `fintype.of_injective` makes this noncomputable
noncomputable instance [fintype G] : fintype (sylow p G) :=
@subtype.fintype _ _ (λ _, classical.prop_decidable _)
  (fintype.of_injective subgroup.carrier (λ _ _ h, subgroup.ext (set.ext_iff.mp h)))

end finite_sylow

open equiv fintype finset mul_action function
open equiv.perm subgroup list quotient_group
open_locale big_operators
universes u v w
variables {G : Type u} {α : Type v} {β : Type w} [group G]

local attribute [instance, priority 10] subtype.fintype set_fintype classical.prop_decidable

lemma quotient_group.card_preimage_mk [fintype G] (s : subgroup G)
  (t : set (quotient s)) : fintype.card (quotient_group.mk ⁻¹' t) =
  fintype.card s * fintype.card t :=
by rw [← fintype.card_prod, fintype.card_congr
  (preimage_mk_equiv_subgroup_times_set _ _)]

namespace sylow

open subgroup submonoid mul_action

lemma mem_fixed_points_mul_left_cosets_iff_mem_normalizer {H : subgroup G}
  [fintype ((H : set G) : Type u)] {x : G} :
  (x : quotient H) ∈ fixed_points H (quotient H) ↔ x ∈ normalizer H :=
⟨λ hx, have ha : ∀ {y : quotient H}, y ∈ orbit H (x : quotient H) → y = x,
  from λ _, ((mem_fixed_points' _).1 hx _),
  (inv_mem_iff _).1 (@mem_normalizer_fintype _ _ _ _inst_2 _ (λ n (hn : n ∈ H),
    have (n⁻¹ * x)⁻¹ * x ∈ H := quotient_group.eq.1 (ha (mem_orbit _ ⟨n⁻¹, H.inv_mem hn⟩)),
    show _ ∈ H, by {rw [mul_inv_rev, inv_inv] at this, convert this, rw inv_inv}
    )),
λ (hx : ∀ (n : G), n ∈ H ↔ x * n * x⁻¹ ∈ H),
(mem_fixed_points' _).2 $ λ y, quotient.induction_on' y $ λ y hy, quotient_group.eq.2
  (let ⟨⟨b, hb₁⟩, hb₂⟩ := hy in
  have hb₂ : (b * x)⁻¹ * y ∈ H := quotient_group.eq.1 hb₂,
  (inv_mem_iff H).1 $ (hx _).2 $ (mul_mem_cancel_left H (H.inv_mem hb₁)).1
  $ by rw hx at hb₂;
    simpa [mul_inv_rev, mul_assoc] using hb₂)⟩

def fixed_points_mul_left_cosets_equiv_quotient (H : subgroup G) [fintype (H : set G)] :
  mul_action.fixed_points H (quotient H) ≃
  quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
@subtype_quotient_equiv_quotient_subtype G (normalizer H : set G) (id _) (id _) (fixed_points _ _)
  (λ a, (@mem_fixed_points_mul_left_cosets_iff_mem_normalizer _ _ _ _inst_2 _).symm)
  (by intros; refl)

/-- If `H` is a `p`-subgroup of `G`, then the index of `H` inside its normalizer is congruent
  mod `p` to the index of `H`.  -/
lemma card_quotient_normalizer_modeq_card_quotient [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H))
  ≡ card (quotient H) [MOD p] :=
begin
  rw [← fintype.card_congr (fixed_points_mul_left_cosets_equiv_quotient H)],
  exact ((is_p_group.of_card hH).card_modeq_card_fixed_points _).symm
end

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`, then the cardinality of the
  normalizer of `H` is congruent mod `p ^ (n + 1)` to the cardinality of `G`.  -/
lemma card_normalizer_modeq_card [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  {H : subgroup G} (hH : fintype.card H = p ^ n) :
  card (normalizer H) ≡ card G [MOD p ^ (n + 1)] :=
have subgroup.comap ((normalizer H).subtype : normalizer H →* G) H ≃ H,
  from set.bij_on.equiv (normalizer H).subtype
    ⟨λ _, id, λ _ _ _ _ h, subtype.val_injective h,
      λ x hx, ⟨⟨x, le_normalizer hx⟩, hx, rfl⟩⟩,
begin
  rw [card_eq_card_quotient_mul_card_subgroup H,
      card_eq_card_quotient_mul_card_subgroup
        (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H),
      fintype.card_congr this, hH, pow_succ],
  exact (card_quotient_normalizer_modeq_card_quotient hH).mul_right' _
end

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup, then `p` divides the
  index of `H` inside its normalizer. -/
lemma prime_dvd_card_quotient_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  hcard ▸ (card_quotient_normalizer_modeq_card_quotient hH).symm,
nat.dvd_of_mod_eq_zero
  (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm)

/-- If `H` is a `p`-subgroup but not a Sylow `p`-subgroup of cardinality `p ^ n`,
  then `p ^ (n + 1)` divides the cardinality of the normalizer of `H`. -/
lemma prime_pow_dvd_card_normalizer [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  p ^ (n + 1) ∣ card (normalizer H) :=
nat.modeq_zero_iff_dvd.1 ((card_normalizer_modeq_card hH).trans
  hdvd.modeq_zero_nat)

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ (n + 1)`
  if `p ^ (n + 1)` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_succ [fintype G] {p : ℕ} {n : ℕ} [hp : fact p.prime]
  (hdvd : p ^ (n + 1) ∣ card G) {H : subgroup G} (hH : fintype.card H = p ^ n) :
  ∃ K : subgroup G, fintype.card K = p ^ (n + 1) ∧ H ≤ K :=
let ⟨s, hs⟩ := exists_eq_mul_left_of_dvd hdvd in
have hcard : card (quotient H) = s * p :=
  (nat.mul_left_inj (show card H > 0, from fintype.card_pos_iff.2
      ⟨⟨1, H.one_mem⟩⟩)).1
    (by rwa [← card_eq_card_quotient_mul_card_subgroup H, hH, hs,
      pow_succ', mul_assoc, mul_comm p]),
have hm : s * p % p =
  card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) % p :=
  card_congr (fixed_points_mul_left_cosets_equiv_quotient H) ▸ hcard ▸
    (is_p_group.of_card hH).card_modeq_card_fixed_points _,
have hm' : p ∣ card (quotient (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H)) :=
  nat.dvd_of_mod_eq_zero
    (by rwa [nat.mod_eq_zero_of_dvd (dvd_mul_left _ _), eq_comm] at hm),
let ⟨x, hx⟩ := @exists_prime_order_of_dvd_card _ (quotient_group.quotient.group _) _ _ hp hm' in
have hequiv : H ≃ (subgroup.comap ((normalizer H).subtype : normalizer H →* G) H) :=
  ⟨λ a, ⟨⟨a.1, le_normalizer a.2⟩, a.2⟩, λ a, ⟨a.1.1, a.2⟩,
    λ ⟨_, _⟩, rfl, λ ⟨⟨_, _⟩, _⟩, rfl⟩,
⟨subgroup.map ((normalizer H).subtype) (subgroup.comap
  (quotient_group.mk' (comap H.normalizer.subtype H)) (gpowers x)),
begin
  show card ↥(map H.normalizer.subtype
    (comap (mk' (comap H.normalizer.subtype H)) (subgroup.gpowers x))) = p ^ (n + 1),
  suffices : card ↥(subtype.val '' ((subgroup.comap (mk' (comap H.normalizer.subtype H))
    (gpowers x)) : set (↥(H.normalizer)))) = p^(n+1),
  { convert this using 2 },
  rw [set.card_image_of_injective
        (subgroup.comap (mk' (comap H.normalizer.subtype H)) (gpowers x) : set (H.normalizer))
        subtype.val_injective,
      pow_succ', ← hH, fintype.card_congr hequiv, ← hx, order_eq_card_gpowers,
      ← fintype.card_prod],
  exact @fintype.card_congr _ _ (id _) (id _) (preimage_mk_equiv_subgroup_times_set _ _)
end,
begin
  assume y hy,
  simp only [exists_prop, subgroup.coe_subtype, mk'_apply, subgroup.mem_map, subgroup.mem_comap],
  refine ⟨⟨y, le_normalizer hy⟩, ⟨0, _⟩, rfl⟩,
  rw [gpow_zero, eq_comm, quotient_group.eq_one_iff],
  simpa using hy
end⟩

/-- If `H` is a subgroup of `G` of cardinality `p ^ n`,
  then `H` is contained in a subgroup of cardinality `p ^ m`
  if `n ≤ m` and `p ^ m` divides the cardinality of `G` -/
theorem exists_subgroup_card_pow_prime_le [fintype G] (p : ℕ) : ∀ {n m : ℕ} [hp : fact p.prime]
  (hdvd : p ^ m ∣ card G) (H : subgroup G) (hH : card H = p ^ n) (hnm : n ≤ m),
  ∃ K : subgroup G, card K = p ^ m ∧ H ≤ K
| n m := λ hp hdvd H hH hnm,
  (lt_or_eq_of_le hnm).elim
    (λ hnm : n < m,
      have h0m : 0 < m, from (lt_of_le_of_lt n.zero_le hnm),
      have wf : m - 1 < m,  from nat.sub_lt h0m zero_lt_one,
      have hnm1 : n ≤ m - 1, from nat.le_sub_right_of_add_le hnm,
      let ⟨K, hK⟩ := @exists_subgroup_card_pow_prime_le n (m - 1) hp
        (nat.pow_dvd_of_le_of_pow_dvd (nat.sub_le_self _ _) hdvd) H hH hnm1 in
      have hdvd' : p ^ ((m - 1) + 1) ∣ card G, by rwa [nat.sub_add_cancel h0m],
      let ⟨K', hK'⟩ := @exists_subgroup_card_pow_succ _ _ _ _ _ hp hdvd' K hK.1 in
      ⟨K', by rw [hK'.1, nat.sub_add_cancel h0m], le_trans hK.2 hK'.2⟩)
    (λ hnm : n = m, ⟨H, by simp [hH, hnm]⟩)

/-- A generalisation of **Sylow's first theorem**. If `p ^ n` divides
  the cardinality of `G`, then there is a subgroup of cardinality `p ^ n` -/
theorem exists_subgroup_card_pow_prime [fintype G] (p : ℕ) {n : ℕ} [fact p.prime]
  (hdvd : p ^ n ∣ card G) : ∃ K : subgroup G, fintype.card K = p ^ n :=
let ⟨K, hK⟩ := exists_subgroup_card_pow_prime_le p hdvd ⊥ (by simp) n.zero_le in
⟨K, hK.1⟩

end sylow
