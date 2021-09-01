import linear_algebra.finite_dimensional
import group_theory.coset

lemma cardinal.to_nat_mul (x y : cardinal) : (x * y).to_nat = x.to_nat * y.to_nat :=
begin
  by_cases hx1 : x = 0,
  { rw [hx1, zero_mul, cardinal.zero_to_nat, zero_mul] },
  by_cases hy1 : y = 0,
  { rw [hy1, mul_zero, cardinal.zero_to_nat, mul_zero] },
  cases lt_or_ge x cardinal.omega with hx2 hx2,
  { cases lt_or_ge y cardinal.omega with hy2 hy2,
    { rw [cardinal.to_nat_apply_of_lt_omega (cardinal.mul_lt_omega hx2 hy2),
          cardinal.to_nat_apply_of_lt_omega hx2, cardinal.to_nat_apply_of_lt_omega hy2,
          ←cardinal.nat_cast_inj, nat.cast_mul,
          ←classical.some_spec (cardinal.lt_omega.mp (cardinal.mul_lt_omega hx2 hy2)),
          ←classical.some_spec (cardinal.lt_omega.mp hx2),
          ←classical.some_spec (cardinal.lt_omega.mp hy2)] },
    { rw [cardinal.to_nat_apply_of_omega_le hy2, mul_zero, cardinal.to_nat_apply_of_omega_le],
      rw [←not_lt, cardinal.mul_lt_omega_iff_of_ne_zero hx1 hy1, not_and_distrib, not_lt, not_lt],
      exact or.inr hy2 } },
  { rw [cardinal.to_nat_apply_of_omega_le hx2, zero_mul, cardinal.to_nat_apply_of_omega_le],
    rw [←not_lt, cardinal.mul_lt_omega_iff_of_ne_zero hx1 hy1, not_and_distrib, not_lt, not_lt],
    exact or.inl hx2 },
end

namespace subgroup

variables {G : Type*} [group G] (H K : subgroup G)

/-- The index of a subgroup as a natural number -/
noncomputable def findex : ℕ :=
(cardinal.mk (quotient_group.quotient H)).to_nat

lemma findex_eq_card [fintype (quotient_group.quotient H)] :
  H.findex = fintype.card (quotient_group.quotient H) :=
cardinal.mk_to_nat_eq_card

lemma findex_mul_card [fintype G] [fintype H] [decidable_pred (∈ H)] :
  H.findex * fintype.card H = fintype.card G :=
begin
  convert H.card_eq_card_quotient_mul_card_subgroup.symm,
  exact H.findex_eq_card,
end

lemma findex_dvd_card [fintype G] [decidable_pred (∈ H)] : H.findex ∣ fintype.card G :=
begin
  convert H.card_quotient_dvd_card,
  exact H.findex_eq_card,
end

variables {H K}

lemma findex_dvd_of_le (h_le : H ≤ K) : K.findex ∣ H.findex :=
begin
  use (cardinal.mk (quotient_group.quotient (H.subgroup_of K))).to_nat,
  rw [findex, findex, ←cardinal.to_nat_mul],
  apply congr_arg cardinal.to_nat,
  apply cardinal.eq_congr,
  sorry,
end

end subgroup
