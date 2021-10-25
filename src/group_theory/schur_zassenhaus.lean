/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import data.set_like.fintype
import group_theory.complement
import group_theory.sylow

/-!
# Complements

In this file we prove the Schur-Zassenhaus theorem.

## Main results

- `exists_right_complement_of_coprime` : If `H : subgroup G` is normal and has order coprime to
  its index, then there exists a subgroup `K` which is a (right) complement of `H`.
- `exists_left_complement_of_coprime` : If `H : subgroup G` is normal and has order coprime to
  its index, then there exists a subgroup `K` which is a (left) complement of `H`.
-/

open_locale big_operators

namespace subgroup

section schur_zassenhaus_abelian

variables {G : Type*} [group G] {H : subgroup G}

@[to_additive] instance : mul_action G (left_transversals (H : set G)) :=
{ smul := λ g T, ⟨left_coset g T, mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr (λ g', by
  { obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (g⁻¹ * g'),
    simp_rw [←mul_assoc, ←mul_inv_rev] at ht1 ht2,
    refine ⟨⟨g * t, mem_left_coset g t.2⟩, ht1, _⟩,
    rintros ⟨_, t', ht', rfl⟩ h,
    exact subtype.ext ((mul_right_inj g).mpr (subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h))) })⟩,
  one_smul := λ T, subtype.ext (one_left_coset T),
  mul_smul := λ g g' T, subtype.ext (left_coset_assoc ↑T g g').symm }

lemma smul_symm_apply_eq_mul_symm_apply_inv_smul
  (g : G) (α : left_transversals (H : set G)) (q : quotient_group.quotient H) :
  ↑((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)).symm q) =
    g * ((equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm
      (g⁻¹ • q : quotient_group.quotient H)) :=
begin
  let w := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)),
  let y := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp (g • α).2)),
  change ↑(y.symm q) = ↑(⟨_, mem_left_coset g (subtype.mem _)⟩ : (g • α).1),
  refine subtype.ext_iff.mp (y.symm_apply_eq.mpr _),
  change q = g • (w (w.symm (g⁻¹ • q : quotient_group.quotient H))),
  rw [equiv.apply_symm_apply, ←mul_smul, mul_inv_self, one_smul],
end

variables [is_commutative H] [fintype (quotient_group.quotient H)]

variables (α β γ : left_transversals (H : set G))

/-- The difference of two left transversals -/
@[to_additive "The difference of two left transversals"]
noncomputable def diff [hH : normal H] : H :=
let α' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp α.2)).symm,
    β' := (equiv.of_bijective _ (mem_left_transversals_iff_bijective.mp β.2)).symm in
∏ (q : quotient_group.quotient H), ⟨(α' q) * (β' q)⁻¹,
  hH.mem_comm (quotient.exact' ((β'.symm_apply_apply q).trans (α'.symm_apply_apply q).symm))⟩

@[to_additive] lemma diff_mul_diff [normal H] : diff α β * diff β γ = diff α γ :=
finset.prod_mul_distrib.symm.trans (finset.prod_congr rfl (λ x hx, subtype.ext
  (by rw [coe_mul, coe_mk, coe_mk, coe_mk, mul_assoc, inv_mul_cancel_left])))

@[to_additive] lemma diff_self [normal H] : diff α α = 1 :=
mul_right_eq_self.mp (diff_mul_diff α α α)

@[to_additive] lemma diff_inv [normal H]: (diff α β)⁻¹ = diff β α :=
inv_eq_of_mul_eq_one ((diff_mul_diff α β α).trans (diff_self α))

lemma smul_diff_smul [hH : normal H] (g : G) :
  diff (g • α) (g • β) = ⟨g * diff α β * g⁻¹, hH.conj_mem (diff α β).1 (diff α β).2 g⟩ :=
begin
  let ϕ : H →* H :=
  { to_fun := λ h, ⟨g * h * g⁻¹, hH.conj_mem h.1 h.2 g⟩,
    map_one' := subtype.ext (by rw [coe_mk, coe_one, mul_one, mul_inv_self]),
    map_mul' := λ h₁ h₂, subtype.ext (by rw [coe_mk, coe_mul, coe_mul, coe_mk, coe_mk, mul_assoc,
      mul_assoc, mul_assoc, mul_assoc, mul_assoc, inv_mul_cancel_left]) },
  refine eq.trans (finset.prod_bij' (λ q _, (↑g)⁻¹ * q) (λ _ _, finset.mem_univ _)
    (λ q _, subtype.ext _) (λ q _, ↑g * q) (λ _ _, finset.mem_univ _)
    (λ q _, mul_inv_cancel_left g q) (λ q _, inv_mul_cancel_left g q)) (ϕ.map_prod _ _).symm,
  change _ * _ = g * (_ * _) * g⁻¹,
  simp_rw [smul_symm_apply_eq_mul_symm_apply_inv_smul, mul_inv_rev, mul_assoc],
  refl,
end

lemma smul_diff [H.normal] (h : H) :
  diff (h • α) β = h ^ H.index * diff α β :=
begin
  rw [diff, diff, index_eq_card, ←finset.card_univ, ←finset.prod_const, ←finset.prod_mul_distrib],
  refine finset.prod_congr rfl (λ q _, _),
  rw [subtype.ext_iff, coe_mul, coe_mk, coe_mk, ←mul_assoc, mul_right_cancel_iff],
  rw [show h • α = (h : G) • α, from rfl, smul_symm_apply_eq_mul_symm_apply_inv_smul],
  rw [mul_left_cancel_iff, ←subtype.ext_iff, equiv.apply_eq_iff_eq, inv_smul_eq_iff],
  exact self_eq_mul_left.mpr ((quotient_group.eq_one_iff _).mpr h.2),
end

variables (H)

instance setoid_diff [H.normal] : setoid (left_transversals (H : set G)) :=
setoid.mk (λ α β, diff α β = 1) ⟨λ α, diff_self α, λ α β h₁,
  by rw [←diff_inv, h₁, one_inv], λ α β γ h₁ h₂, by rw [←diff_mul_diff, h₁, h₂, one_mul]⟩

/-- The quotient of the transversals of an abelian normal `N` by the `diff` relation -/
def quotient_diff [H.normal] :=
quotient H.setoid_diff

instance [H.normal] : inhabited H.quotient_diff :=
quotient.inhabited

variables {H}

instance [H.normal] : mul_action G H.quotient_diff :=
{ smul := λ g, quotient.map (λ α, g • α) (λ α β h, (smul_diff_smul α β g).trans
    (subtype.ext (mul_inv_eq_one.mpr (mul_right_eq_self.mpr (subtype.ext_iff.mp h))))),
  mul_smul := λ g₁ g₂ q, quotient.induction_on q (λ α, congr_arg quotient.mk (mul_smul g₁ g₂ α)),
  one_smul := λ q, quotient.induction_on q (λ α, congr_arg quotient.mk (one_smul G α)) }

variables [fintype H]

lemma exists_smul_eq [H.normal] (α β : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ h : H, h • α = β :=
quotient.induction_on α (quotient.induction_on β
  (λ β α, exists_imp_exists (λ n, quotient.sound)
    ⟨(pow_coprime hH).symm (diff α β)⁻¹, by
    { change diff ((_ : H) • _) _ = 1,
      rw smul_diff,
      change pow_coprime hH ((pow_coprime hH).symm (diff α β)⁻¹) * (diff α β) = 1,
      rw [equiv.apply_symm_apply, inv_mul_self] }⟩))

lemma smul_left_injective [H.normal] (α : H.quotient_diff)
  (hH : nat.coprime (fintype.card H) H.index) :
  function.injective (λ h : H, h • α) :=
λ h₁ h₂, begin
  refine quotient.induction_on α (λ α hα, _),
  replace hα : diff (h₁ • α) (h₂ • α) = 1 := quotient.exact hα,
  rw [smul_diff, ←diff_inv, smul_diff, diff_self, mul_one, mul_inv_eq_one] at hα,
  exact (pow_coprime hH).injective hα,
end

lemma is_complement_stabilizer_of_coprime [fintype G] [H.normal] {α : H.quotient_diff}
  (hH : nat.coprime (fintype.card H) H.index) :
  is_complement (H : set G) (mul_action.stabilizer G α : set G) :=
begin
  classical,
  let ϕ : H ≃ mul_action.orbit G α := equiv.of_bijective (λ h, ⟨h • α, h, rfl⟩)
    ⟨λ h₁ h₂ hh, smul_left_injective α hH (subtype.ext_iff.mp hh),
      λ β, exists_imp_exists (λ h hh, subtype.ext hh) (exists_smul_eq α β hH)⟩,
  have key := card_eq_card_quotient_mul_card_subgroup (mul_action.stabilizer G α),
  rw ← fintype.card_congr (ϕ.trans (mul_action.orbit_equiv_quotient_stabilizer G α)) at key,
  apply is_complement_of_coprime key.symm,
  rw [card_eq_card_quotient_mul_card_subgroup H, mul_comm, mul_right_inj'] at key,
  { rwa [←key, ←index_eq_card] },
  { rw [←pos_iff_ne_zero, fintype.card_pos_iff],
    apply_instance },
end

theorem exists_right_complement_of_coprime_aux [fintype G] [H.normal]
  (hH : nat.coprime (fintype.card H) H.index) :
  ∃ K : subgroup G, is_complement (H : set G) (K : set G) :=
nonempty_of_inhabited.elim
  (λ α : H.quotient_diff, ⟨mul_action.stabilizer G α, is_complement_stabilizer_of_coprime hH⟩)

end schur_zassenhaus_abelian

lemma index_eq_one {G : Type*} [group G] {H : subgroup G} : H.index = 1 ↔ H = ⊤ :=
⟨λ h, quotient_group.subgroup_eq_top_of_subsingleton H (cardinal.to_nat_eq_one_iff_unique.mp h).1,
  λ h, (congr_arg index h).trans index_top⟩

lemma index_ne_zero_of_fintype {G : Type*} [group G] {H : subgroup G}
  [hH : fintype (quotient_group.quotient H)] : H.index ≠ 0 :=
by rw index_eq_card; exact fintype.card_ne_zero

lemma one_lt_index_of_ne_top {G : Type*} [group G] {H : subgroup G}
  [fintype (quotient_group.quotient H)] (hH : H ≠ ⊤) : 1 < H.index :=
nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨index_ne_zero_of_fintype, mt index_eq_one.mp hH⟩

lemma _root_.is_p_group.bot_lt_center {p : ℕ} [fact p.prime]
  {G : Type*} [group G] [fintype G] (hG : is_p_group p G) :
  ⊥ < center G :=
begin
  classical,
  have hG' := hG.of_equiv conj_act.to_conj_act,
  have need : p ∣ fintype.card G := sorry,
  have key' : (1 : G) ∈ mul_action.fixed_points (conj_act G) G,
  { intro g,
    exact mul_distrib_mul_action.smul_one g, },
  obtain ⟨g, hg⟩ := hG'.exists_fixed_point_of_prime_dvd_card_of_fixed_point G need key',
  replace hg : g ∈ center G,
  { intro h, },
end

open_locale classical

lemma silly_lemma {G : Type*} [group G] [fintype G] {H : subgroup G} {n : ℕ} :
  fintype.card H * n = fintype.card G ↔ H.index = n :=
begin
  sorry,
end

universe u

namespace schur_zassenhaus_induction

variables {G : Type u} [group G] [fintype G] {N : subgroup G} [normal N]
  (h1 : nat.coprime (fintype.card N) N.index)
  (h2 : ∀ (G' : Type u) [group G'] [fintype G'], by exactI
    ∀ (hG'3 : fintype.card G' < fintype.card G)
    {N' : subgroup G'} [N'.normal] (hN : nat.coprime (fintype.card N') N'.index),
    ∃ H' : subgroup G', is_complement (N' : set G') (H' : set G'))
  (h3 : ∀ H : subgroup G, ¬ is_complement (N : set G) (H : set G))

include h1 h2 h3

lemma N_ne_bot : N ≠ ⊥ :=
begin
  tactic.unfreeze_local_instances,
  rintro rfl,
  exact h3 ⊤ is_complement_singleton_top,
end

lemma N_ne_top : N ≠ ⊤ :=
begin
  tactic.unfreeze_local_instances,
  rintro rfl,
  exact h3 ⊥ is_complement_top_singleton,
end

lemma step1 (K : subgroup G) (hK1 : K ⊔ N = ⊤) : K = ⊤ :=
begin
  contrapose! h3 with hK2,
  have h31 : fintype.card K < fintype.card G,
  { rw ← K.index_mul_card,
    exact lt_mul_of_one_lt_left fintype.card_pos (one_lt_index_of_ne_top hK2) },
  have h32 : (N.comap K.subtype).index = N.index,
  { rw [←N.relindex_top_right, ←hK1],
    exact relindex_eq_relindex_sup K N },
  have h33 : nat.coprime (fintype.card (N.comap K.subtype)) (N.comap K.subtype).index,
  { rw h32,
    exact h1.coprime_dvd_left (card_comap_dvd_of_injective N K.subtype subtype.coe_injective) },
  obtain ⟨H, hH⟩ := h2 K h31 h33,
  replace hH := h32.symm.trans (silly_lemma.mp (hH.card_mul)),
  replace hH : N.index = fintype.card (H.map K.subtype) :=
  hH.trans (set.card_image_of_injective _ subtype.coe_injective).symm,
  refine ⟨H.map K.subtype, is_complement_of_coprime (silly_lemma.mpr hH) _⟩,
  by rwa ← hH,
end

lemma step2 (K : subgroup G) [K.normal] (hK1 : K ≤ N) : K = ⊥ ∨ K = N :=
begin
  have h4 := step1 h1 h2 h3,
  contrapose! h4 with hK2,
  have h41 : fintype.card (quotient_group.quotient K) < fintype.card G,
  { rw [←index_eq_card, ←K.index_mul_card],
    refine lt_mul_of_one_lt_right (nat.pos_of_ne_zero index_ne_zero_of_fintype)
      (K.one_lt_card_iff_ne_bot.mpr hK2.1) },
  have h42 : nat.coprime (fintype.card (N.map (quotient_group.mk' K)))
    (N.map (quotient_group.mk' K)).index,
  { -- card goes down, index stays the same
    sorry },
  obtain ⟨H, hh⟩ := h2 (quotient_group.quotient K) h41 h42,
  refine ⟨H.comap (quotient_group.mk' K), _, _⟩,
  { have key : (N.map (quotient_group.mk' K)).comap (quotient_group.mk' K) = N,
    { refine comap_map_eq_self _,
      rwa quotient_group.ker_mk },
    rw [←key, comap_sup_eq],
    { -- is_complement.sup_eq_top
      -- comap_top (already in library)
      sorry },
    { exact quotient.surjective_quotient_mk' } },
  { sorry }
end

lemma step3 : (fintype.card N).min_fac.prime :=
(nat.min_fac_prime (N.one_lt_card_iff_ne_bot.mpr (N_ne_bot h1 h2 h3)).ne')

lemma step4 {P : sylow (fintype.card N).min_fac N} : P.1 ≠ ⊥ :=
begin
  sorry
end

lemma step5 : is_p_group (fintype.card N).min_fac N :=
begin
  let p := (fintype.card N).min_fac,
  haveI : fact (p.prime) := ⟨step3 h1 h2 h3⟩,
  refine sylow.nonempty.elim (λ P : sylow p N, P.2.of_surjective P.1.subtype _),
  rw [←monoid_hom.range_top_iff_surjective, subtype_range],

  haveI : (P.1.map N.subtype).normal := normalizer_eq_top.mp
    (step1 h1 h2 h3 (P.1.map N.subtype).normalizer P.normalizer_sup_eq_top),
  have key := step2 h1 h2 h3 (P.1.map N.subtype) P.1.map_subtype_le,
  rw ← map_bot N.subtype at key,
  conv at key { congr, skip, to_rhs, rw [←N.subtype_range, monoid_hom.range_eq_map] },
  have inj := map_injective (show function.injective N.subtype, from subtype.coe_injective),
  rw [inj.eq_iff, inj.eq_iff] at key,
  exact key.resolve_left (step4 h1 h2 h3),
end

lemma step6 : is_commutative N :=
begin
  haveI : ((center N).map N.subtype).normal,
  { -- characteristic subgroups
    sorry },
  have key := step2 h1 h2 h3 ((center N).map N.subtype) (center N).map_subtype_le,
  sorry,
end

lemma step7 : false :=
begin
  haveI := step6 h1 h2 h3,
  exact not_exists_of_forall_not h3 (exists_right_complement_of_coprime_aux h1),
end

end schur_zassenhaus_induction

lemma exists_right_complement_of_coprime_aux'
  {n : ℕ} {G : Type u} [group G] [fintype G] (hG : fintype.card G = n)
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (N : set G) (H : set G) :=
begin
  tactic.unfreeze_local_instances,
  revert G,
  apply nat.strong_induction_on n,
  rintros n ih G _ _ rfl N _ hN,
  exact not_forall_not.mp
    (schur_zassenhaus_induction.step7 hN (λ G' _ _ hG', by { apply ih _ hG', refl })),
end

lemma card_mul_index {G : Type*} [group G] (H : subgroup G) : nat.card H * H.index = nat.card G :=
by rw [←relindex_bot_left, ←index_bot]; exact relindex_mul_index bot_le

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement_of_coprime {G : Type u} [group G] [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (N : set G) (H : set G) :=
exists_right_complement_of_coprime_aux' rfl hN

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (right) complement of `H`. -/
theorem exists_right_complement_of_coprime' {G : Type u} [group G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement (N : set G) (H : set G) :=
begin
  by_cases hN1 : nat.card N = 0,
  { rw [hN1, nat.coprime_zero_left, index_eq_one] at hN,
    rw hN,
    exact ⟨⊥, is_complement_top_singleton⟩ },
  by_cases hN2 : N.index = 0,
  { rw [hN2, nat.coprime_zero_right] at hN,
    haveI := (cardinal.to_nat_eq_one_iff_unique.mp hN).1,
    rw N.eq_bot_of_subsingleton,
    exact ⟨⊤, is_complement_singleton_top⟩ },
  have hN3 : nat.card G ≠ 0,
  { rw ← N.card_mul_index,
    exact mul_ne_zero hN1 hN2 },
  haveI := (cardinal.lt_omega_iff_fintype.mp
    (lt_of_not_ge (mt cardinal.to_nat_apply_of_omega_le hN3))).some,
  rw nat.card_eq_fintype_card at hN,
  exact exists_right_complement_of_coprime hN,
end

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement_of_coprime {G : Type u} [group G] [fintype G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (fintype.card N) N.index) :
  ∃ H : subgroup G, is_complement (H : set G) (N : set G) :=
Exists.imp (λ _, is_complement.symm) (exists_right_complement_of_coprime hN)

/-- **Schur-Zassenhaus** for normal subgroups:
  If `H : subgroup G` is normal, and has order coprime to its index, then there exists
  a subgroup `K` which is a (left) complement of `H`. -/
theorem exists_left_complement_of_coprime' {G : Type u} [group G]
  {N : subgroup G} [N.normal] (hN : nat.coprime (nat.card N) N.index) :
  ∃ H : subgroup G, is_complement (H : set G) (N : set G) :=
Exists.imp (λ _, is_complement.symm) (exists_right_complement_of_coprime' hN)

end subgroup
