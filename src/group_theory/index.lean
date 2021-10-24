/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

import group_theory.quotient_group
import set_theory.fincard

/-!
# Index of a Subgroup

In this file we define the index of a subgroup, and prove several divisibility properties.

## Main definitions

- `H.index` : the index of `H : subgroup G` as a natural number,
  and returns 0 if the index is infinite.
- `H.relindex K` : the relative index of `H : subgroup G` in `K : subgroup G` as a natural number,
  and returns 0 if the relative index is infinite.

# Main results

- `index_mul_card` : `H.index * fintype.card H = fintype.card G`
- `index_dvd_card` : `H.index ∣ fintype.card G`
- `index_eq_mul_of_le` : If `H ≤ K`, then `H.index = K.index * (H.subgroup_of K).index`
- `index_dvd_of_le` : If `H ≤ K`, then `K.index ∣ H.index`
- `relindex_mul_relindex` : `relindex` is multiplicative in towers

-/

namespace subgroup

open_locale cardinal

variables {G : Type*} [group G] (H K L : subgroup G)

/-- The index of a subgroup as a natural number, and returns 0 if the index is infinite. -/
@[to_additive "The index of a subgroup as a natural number,
and returns 0 if the index is infinite."]
noncomputable def index : ℕ :=
nat.card (quotient_group.quotient H)

/-- The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite. -/
@[to_additive "The relative index of a subgroup as a natural number,
  and returns 0 if the relative index is infinite."]
noncomputable def relindex : ℕ :=
(H.subgroup_of K).index

@[to_additive] lemma index_comap_of_surjective {G' : Type*} [group G'] {f : G' →* G}
  (hf : function.surjective f) : (H.comap f).index = H.index :=
begin
  letI := quotient_group.left_rel H,
  letI := quotient_group.left_rel (H.comap f),
  have key : ∀ x y : G', setoid.r x y ↔ setoid.r (f x) (f y) :=
  λ x y, iff_of_eq (congr_arg (∈ H) (by rw [f.map_mul, f.map_inv])),
  refine cardinal.to_nat_congr (equiv.of_bijective (quotient.map' f (λ x y, (key x y).mp)) ⟨_, _⟩),
  { simp_rw [←quotient.eq'] at key,
    refine quotient.ind' (λ x, _),
    refine quotient.ind' (λ y, _),
    exact (key x y).mpr },
  { refine quotient.ind' (λ x, _),
    obtain ⟨y, hy⟩ := hf x,
    exact ⟨y, (quotient.map'_mk' f _ y).trans (congr_arg quotient.mk' hy)⟩ },
end

@[to_additive] lemma index_comap {G' : Type*} [group G'] (f : G' →* G) :
  (H.comap f).index = H.relindex f.range :=
eq.trans (congr_arg index (by refl))
  ((H.subgroup_of f.range).index_comap_of_surjective f.range_restrict_surjective)

variables {H K L}

@[to_additive] lemma relindex_mul_index (h : H ≤ K) : H.relindex K * K.index = H.index :=
((mul_comm _ _).trans (cardinal.to_nat_mul _ _).symm).trans
  (congr_arg cardinal.to_nat (equiv.cardinal_eq (quotient_equiv_prod_of_le h))).symm

@[to_additive] lemma index_dvd_of_le (h : H ≤ K) : K.index ∣ H.index :=
dvd_of_mul_left_eq (H.relindex K) (relindex_mul_index h)

@[to_additive] lemma relindex_subgroup_of (hKL : K ≤ L) :
  (H.subgroup_of L).relindex (K.subgroup_of L) = H.relindex K :=
((index_comap (H.subgroup_of L) (inclusion hKL)).trans (congr_arg _ (inclusion_range hKL))).symm

variables (H K L)

@[to_additive] lemma relindex_mul_relindex (hHK : H ≤ K) (hKL : K ≤ L) :
  H.relindex K * K.relindex L = H.relindex L :=
begin
  rw [←relindex_subgroup_of hKL],
  exact relindex_mul_index (λ x hx, hHK hx),
end

@[simp, to_additive] lemma index_top : (⊤ : subgroup G).index = 1 :=
cardinal.to_nat_eq_one_iff_unique.mpr ⟨quotient_group.subsingleton_quotient_top, ⟨1⟩⟩

@[simp, to_additive] lemma index_bot : (⊥ : subgroup G).index = nat.card G :=
cardinal.to_nat_congr (quotient_group.quotient_bot.to_equiv)

@[to_additive] lemma index_bot_eq_card [fintype G] : (⊥ : subgroup G).index = fintype.card G :=
index_bot.trans nat.card_eq_fintype_card

@[simp, to_additive] lemma relindex_top_left : (⊤ : subgroup G).relindex H = 1 :=
index_top

@[simp, to_additive] lemma relindex_top_right : H.relindex ⊤ = H.index :=
by rw [←relindex_mul_index (show H ≤ ⊤, from le_top), index_top, mul_one]

@[simp, to_additive] lemma relindex_bot_left : (⊥ : subgroup G).relindex H = nat.card H :=
by rw [relindex, bot_subgroup_of, index_bot]

@[to_additive] lemma relindex_bot_left_eq_card [fintype H] :
  (⊥ : subgroup G).relindex H = fintype.card H :=
H.relindex_bot_left.trans nat.card_eq_fintype_card

@[simp, to_additive] lemma relindex_bot_right : H.relindex ⊥ = 1 :=
by rw [relindex, subgroup_of_bot_eq_top, index_top]

@[simp, to_additive] lemma relindex_self : H.relindex H = 1 :=
by rw [relindex, subgroup_of_self, index_top]

@[to_additive] lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
nat.card_eq_fintype_card

@[to_additive] lemma index_mul_card [fintype G] [hH : fintype H] :
  H.index * fintype.card H = fintype.card G :=
by rw [←relindex_bot_left_eq_card, ←index_bot_eq_card, mul_comm]; exact relindex_mul_index bot_le

@[to_additive] lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  exact ⟨fintype.card H, H.index_mul_card.symm⟩,
end

lemma relindex_eq_zero_of_le  (h : K ≤ L) (h2 : H.relindex K = 0) : H.relindex L = 0 :=
cardinal.to_nat_eq_zero_of_injective (quotient_group.le_quot_map_injective H L K h ) h2

lemma index_eq_zero_of_le {H K : subgroup G} (h : H ≤ K) (h1 : K.index = 0) : H.index = 0 :=
by rw [←subgroup.relindex_mul_index h, h1, mul_zero]

lemma inf_relindex_inf : (H ⊓ K).relindex (K ⊓ L) = H.relindex (K ⊓ L) :=
begin
  simp_rw subgroup.relindex,
  apply congr_arg,
  ext,
  have xp:=x.property,
  simp only [subgroup.mem_subgroup_of, and_iff_left_iff_imp, subgroup.mem_inf,
    subtype.val_eq_coe] at *,
  simp only [xp, implies_true_iff],
end

lemma inf_relindex_subgroup_of :
  ((H ⊓ K).subgroup_of L).relindex (K.subgroup_of L) = H.relindex (K ⊓ L) :=
begin
  have h0: K ⊓ L ≤ L, by {simp only [inf_le_right],},
  rw [← subgroup.subgroup_of_inf_right K L, ← inf_relindex_inf],
  apply subgroup.relindex_subgroup_of h0,
end

lemma inf_ind_prod  (h : (H ⊓ K).relindex L = 0)  :  H.relindex L = 0 ∨ K.relindex (L ⊓ H) = 0 :=
begin
  have h1 : (subgroup.subgroup_of (H ⊓ K)  L) ≤ (subgroup.subgroup_of H  L),
    by {apply subgroup.subgroup_of_mono_left, simp only [inf_le_left],},
  have h2 := subgroup.relindex_mul_index h1,
  simp_rw subgroup.relindex at h,
  rw h at h2,
  simp only [nat.mul_eq_zero] at h2,
  cases h2,
  rw [inf_comm, ← inf_relindex_subgroup_of K H L, inf_comm],
  simp only [h2, eq_self_iff_true, or_true],
  simp_rw subgroup.relindex,
  simp only [h2, true_or, eq_self_iff_true],
 end

lemma relindex_ne_zero_trans (hhk : H.relindex K ≠ 0) (hkl : K.relindex L ≠ 0) :
   H.relindex L  ≠ 0 :=
begin
  by_contradiction,
  simp only [not_not, ne.def] at *,
  have s1 : (H ⊓ K).subgroup_of L ≤ H.subgroup_of L ,
    by {apply subgroup.subgroup_of_mono_left, simp only [inf_le_left],},
  have H2 := (index_eq_zero_of_le s1) h,
  have H3 := inf_ind_prod K H L,
  have hh0: L ⊓ K ≤ K, by {simp only [inf_le_right],},
  have H4 := relindex_eq_zero_of_le H  (L ⊓ K) K hh0,
  rw inf_comm at H2,
  have H5 := H3 H2,
  cases H5,
  rw H5 at hkl,
  simp only [eq_self_iff_true, not_true, false_and] at hkl,
  exact hkl,
  have H6 := H4 H5,
  rw H6 at hhk,
  simp only [eq_self_iff_true, not_true, false_and] at hhk,
  exact hhk,
end

end subgroup
