import group_theory.coset
import set_theory.cardinal

variables {G : Type*} [group G] (H : subgroup G)

lemma quotient_group.mk_out'_eq_mul (g : G) :
  ∃ h : H, (quotient_group.mk g : quotient_group.quotient H).out' = g * h :=
⟨⟨g⁻¹ * (quotient_group.mk g).out', quotient_group.eq'.mp (quotient_group.mk g).out_eq'.symm⟩,
  by rw [H.coe_mk, mul_inv_cancel_left]⟩

variables {H}

lemma quotient_group.mk_mul_of_mem (g₁ g₂ : G) (hg₂ : g₂ ∈ H) :
  (quotient_group.mk (g₁ * g₂) : quotient_group.quotient H) = quotient_group.mk g₁ :=
by rwa [quotient_group.eq', mul_inv_rev, inv_mul_cancel_right, H.inv_mem_iff]

namespace subgroup

variables (H)

/-- The index of a subgroup as a natural number -/
noncomputable def index : ℕ :=
(cardinal.mk (quotient_group.quotient H)).to_nat

lemma index_eq_card [fintype (quotient_group.quotient H)] :
  H.index = fintype.card (quotient_group.quotient H) :=
cardinal.mk_to_nat_eq_card

lemma index_mul_card [fintype G] [fintype H] :
  H.index * fintype.card H = fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  convert H.card_eq_card_quotient_mul_card_subgroup.symm,
end

lemma index_dvd_card [fintype G] : H.index ∣ fintype.card G :=
begin
  classical,
  rw H.index_eq_card,
  convert H.card_quotient_dvd_card,
end

variables {H} {K : subgroup G}

/-- If `H ≤ K` then `G/H ≃ G/K × K/H` -/
noncomputable def quotient_equiv_prod_of_le (h_le : H ≤ K) : quotient_group.quotient H ≃
  quotient_group.quotient K × quotient_group.quotient (H.subgroup_of K) :=
{ to_fun := λ a, ⟨quotient_group.mk a.out', quotient_group.mk
    ⟨(quotient_group.mk a.out' : quotient_group.quotient K).out'⁻¹ * a.out',
      by rw [←quotient_group.eq', quotient_group.out_eq']⟩⟩,
  inv_fun := λ a, quotient_group.mk (a.1.out' * a.2.out'),
  left_inv := λ a, by
  { obtain ⟨x₁, h₁⟩ := quotient_group.mk_out'_eq_mul K a.out',
    obtain ⟨x₂, h₂⟩ := quotient_group.mk_out'_eq_mul (H.subgroup_of K) x₁⁻¹,
    simp_rw [h₁, mul_inv_rev, inv_mul_cancel_right, ←K.coe_inv, subtype.coe_eta],
    simp_rw [h₂, K.coe_mul, K.coe_inv, mul_assoc, mul_inv_cancel_left],
    exact (quotient_group.mk_mul_of_mem a.out' x₂ x₂.2).trans a.out_eq' },
  right_inv := λ a, by
  { obtain ⟨x, h⟩ := quotient_group.mk_out'_eq_mul H (a.1.out' * a.2.out'),
    simp_rw [h, mul_assoc, quotient_group.mk_mul_of_mem a.1.out' (a.2.out' * x)
      (K.mul_mem a.2.out'.2 (h_le x.2)), quotient_group.out_eq', inv_mul_cancel_left],
    change (a.1, quotient_group.mk (⟨(a.2.out' * ⟨x, h_le x.2⟩ : K), _⟩ : K)) = a,
    simp_rw subtype.coe_eta,
    exact prod.ext rfl ((quotient_group.mk_mul_of_mem a.2.out' ⟨x, h_le x.2⟩ (by exact x.2)).trans
      a.2.out_eq') } }

lemma index_eq_mul_of_le (h_le : H ≤ K) : H.index = K.index * (H.subgroup_of K).index :=
(congr_arg cardinal.to_nat (by exact cardinal.eq_congr (quotient_equiv_prod_of_le h_le))).trans
  (cardinal.to_nat_mul _ _)

lemma index_dvd_of_le (h_le : H ≤ K) : K.index ∣ H.index :=
⟨(H.subgroup_of K).index, index_eq_mul_of_le h_le⟩

end subgroup
