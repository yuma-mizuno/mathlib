import group_theory.coset
import set_theory.cardinal

namespace subgroup

variables {G : Type*} [group G] (H : subgroup G)

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

lemma key_lemma1 (g : G) :
  ∃ h : H, (quotient_group.mk g : quotient_group.quotient H).out' = g * h :=
⟨⟨g⁻¹ * (quotient_group.mk g).out', quotient_group.eq'.mp (quotient_group.mk g).out_eq'.symm⟩,
  by rw [H.coe_mk, mul_inv_cancel_left]⟩

variables {H}

lemma key_lemma2 (g₁ g₂ : G) (hg₂ : g₂ ∈ H) :
  (quotient_group.mk (g₁ * g₂) : quotient_group.quotient H) = quotient_group.mk g₁ :=
by rwa [quotient_group.eq', mul_inv_rev, inv_mul_cancel_right, H.inv_mem_iff]

variables {K : subgroup G}

noncomputable def tada (h_le : H ≤ K) : quotient_group.quotient H ≃
  quotient_group.quotient K × quotient_group.quotient (H.subgroup_of K) :=
{ to_fun := λ a, ⟨quotient_group.mk a.out', quotient_group.mk
    ⟨(quotient_group.mk a.out' : quotient_group.quotient K).out'⁻¹ * a.out',
      by rw [←quotient_group.eq', quotient_group.out_eq']⟩⟩,
  inv_fun := λ a, quotient_group.mk (a.1.out' * a.2.out'),
  left_inv := λ a, by
  { obtain ⟨x₁, h₁⟩ := K.key_lemma1 a.out',
    obtain ⟨x₂, h₂⟩ := (H.subgroup_of K).key_lemma1 x₁⁻¹,
    simp_rw [h₁, mul_inv_rev, inv_mul_cancel_right, ←K.coe_inv, subtype.coe_eta],
    simp_rw [h₂, K.coe_mul, K.coe_inv, mul_assoc, mul_inv_cancel_left],
    exact (key_lemma2 a.out' x₂ x₂.2).trans a.out_eq' },
  right_inv := λ a, by
  { obtain ⟨x, h⟩ := H.key_lemma1 (a.1.out' * a.2.out'),
    simp_rw [h, mul_assoc, key_lemma2 a.1.out' (a.2.out' * x) (K.mul_mem a.2.out'.2 (h_le x.2)),
      quotient_group.out_eq', inv_mul_cancel_left],
    change (a.1, quotient_group.mk (⟨(a.2.out' * ⟨x, h_le x.2⟩ : K), _⟩ : K)) = a,
    simp_rw subtype.coe_eta,
    exact prod.ext rfl ((key_lemma2 a.2.out' ⟨x, h_le x.2⟩ (by exact x.2)).trans a.2.out_eq') } }

lemma findex_dvd_of_le (h_le : H ≤ K) : K.findex ∣ H.findex :=
begin
  refine ⟨(H.subgroup_of K).findex, eq.trans _ (cardinal.to_nat_mul _ _)⟩,
  exact congr_arg cardinal.to_nat (cardinal.eq_congr (tada h_le)),
end

end subgroup
