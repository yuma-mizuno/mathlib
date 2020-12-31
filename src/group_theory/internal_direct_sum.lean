/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import group_theory.subgroup

/-!


-/

variables {A : Type*} [comm_group A]

namespace subgroup

lemma mem_sup_iff_exists_mul {s t : subgroup A} {x : A} :
  x ∈ s ⊔ t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x :=
begin
  split,
  { rw [← s.closure_eq, ← t.closure_eq, ← closure_union, subgroup.mem_closure,
      closure_eq, closure_eq],
    intro h1,
    apply h1 ⟨{ x | ∃ y z, y ∈ s ∧ z ∈ t ∧ y * z = x}, ⟨1, 1, s.one_mem, t.one_mem, mul_one 1⟩,
      _, _⟩ (set.union_subset _ _),
    { rintros x y ⟨xs, xt, hxs, hxt, rfl⟩ ⟨ys, yt, hys, hyt, rfl⟩,
        refine ⟨xs * ys, xt * yt, s.mul_mem hxs hys, t.mul_mem hxt hyt, _⟩,
        rw [mul_assoc, ← mul_assoc ys, mul_comm ys, ← mul_assoc,
          ← mul_assoc, mul_assoc _ ys] },
      { rintros _ ⟨x, y, hx, hy, rfl⟩,
        refine ⟨x⁻¹, y⁻¹, s.inv_mem hx, t.inv_mem hy, _⟩,
        rw [mul_comm, mul_inv_rev] },
      { intros x hx,
        refine ⟨x, 1, hx, t.one_mem, mul_one x⟩ },
      { intros x hx,
        refine ⟨1, x, s.one_mem, hx, one_mul x⟩ } },
  { rintros ⟨y, z, ⟨hy, hz, rfl⟩⟩,
    apply subgroup.mul_mem (s ⊔ t) (subgroup.mem_sup_left hy) (subgroup.mem_sup_right hz) }
end

def internal_sum_hom (s t : subgroup A) : s × t →* (s ⊔ t : subgroup A) :=
{ to_fun := λ x, ⟨↑x.fst * ↑x.snd, subgroup.mul_mem (s ⊔ t)
                  (subgroup.mem_sup_left x.fst.prop) (subgroup.mem_sup_right x.snd.prop)⟩,
  map_one' := mul_one 1,
  map_mul' := λ x y, by { ext,
    simp only [prod.snd_mul, prod.fst_mul, subgroup.coe_mul, subtype.coe_mk],
    rw [mul_assoc, ← mul_assoc ↑y.fst, mul_comm ↑y.fst, ← mul_assoc,
        ← mul_assoc, mul_assoc _ ↑y.fst] } }

@[simp] lemma coe_internal_sum_hom {s t : subgroup A} {x : s × t} :
  (↑(internal_sum_hom s t x) : A) = ↑x.fst * ↑x.snd := rfl

lemma internal_sum_hom_surjective {s t : subgroup A} :
  function.surjective (internal_sum_hom s t) :=
λ ⟨x, hx⟩, begin
  rcases mem_sup_iff_exists_mul.1 hx with ⟨y, z, hy, hz, rfl⟩,
  refine ⟨⟨⟨y, hy⟩, ⟨z, hz⟩⟩, _⟩,
  ext,
  simp,
end

lemma internal_sum_hom_bijective_of_disjoint {s t : subgroup A} (h : disjoint s t) :
  function.bijective (internal_sum_hom s t) :=
⟨λ ⟨⟨xs, hxs⟩, ⟨xt, hxt⟩⟩ ⟨⟨ys, hys⟩, ⟨yt, hyt⟩⟩ hxy, begin
  replace hxy : (↑((s.internal_sum_hom t) (⟨xs, hxs⟩, ⟨xt, hxt⟩)) : A) =
    (s.internal_sum_hom t) (⟨ys, hys⟩, ⟨yt, hyt⟩) := congr rfl hxy,
  simp only [coe_mk, coe_internal_sum_hom] at hxy,
  rw [← eq_mul_inv_iff_mul_eq, mul_assoc, eq_comm, ← eq_inv_mul_iff_mul_eq] at hxy,
  ext,
  { simp only [coe_mk],
    rw [eq_comm, ← mul_one ys, ← eq_inv_mul_iff_mul_eq, eq_comm,
      ← mem_bot, ← eq_bot_iff.2 h, mem_inf],
    refine ⟨s.mul_mem (s.inv_mem hys) hxs, _⟩,
    rw ← hxy,
    exact t.mul_mem hyt (t.inv_mem hxt) },
  { simp only [coe_mk],
    rw [← one_mul xt, ← eq_mul_inv_iff_mul_eq, eq_comm, ← mem_bot, ← eq_bot_iff.2 h, mem_inf],
    refine ⟨_, t.mul_mem hyt (t.inv_mem hxt)⟩,
    rw hxy,
    exact s.mul_mem (s.inv_mem hys) hxs },
end, internal_sum_hom_surjective⟩

noncomputable def internal_direct_sum_equiv {s t : subgroup A} (h : disjoint s t) :
  s × t ≃* (s ⊔ t : subgroup A) :=
mul_equiv.of_bijective (internal_sum_hom s t) (internal_sum_hom_bijective_of_disjoint h)

end subgroup
