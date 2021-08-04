/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import linear_algebra.basic
import data.complex.basic

namespace complex

/-- Complex conjugate as a ring equiv, which it probably should be in mathlib... -/
def cconj : ℂ ≃+* ℂ :=
{ to_fun := conj,
  inv_fun := conj,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  ..conj }

@[simp] lemma cconj_apply (x : ℂ) : cconj x = conj x := rfl
@[simp] lemma cconj_symm_apply (x : ℂ) : cconj.symm x = conj x := rfl

end complex

namespace ring_equiv_inv_pair

instance cconj : ring_equiv_inv_pair complex.cconj complex.cconj := ⟨ring_equiv.ext $ λ x, by simp⟩
instance complex_refl : ring_equiv_inv_pair (ring_equiv.refl ℂ) (ring_equiv.refl ℂ) :=
ring_equiv_inv_pair.ids

end ring_equiv_inv_pair

--namespace ring_equiv_comp_triple
--
--instance cconj_cconj : ring_equiv_comp_triple complex.cconj complex.cconj (ring_equiv.refl ℂ) :=
--⟨ring_equiv.ext $ λ x, by simp⟩
--
--end ring_equiv_comp_triple

notation M ` →ₗ* ` M₂:0 := linear_map complex.cconj M M₂
notation M ` ≃ₗ* ` M₂:0 := @linear_equiv ℂ ℂ _ _ complex.cconj complex.cconj
  ring_equiv_inv_pair.cconj ring_equiv_inv_pair.cconj M M₂ _ _ _ _

notation f ` trans* ` g := @linear_equiv.transₛₗ ℂ ℂ ℂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f g

variables {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} --{R : Type*} [semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module ℂ M₁] [module ℂ M₂] [module ℂ M₃] --[module R M₁] [module R M₂]
variables (f : M₁ →ₗ* M₂) (g : M₂ →ₗ* M₃) (f' : M₁ →ₗ[ℂ] M₂) (g' : M₂ →ₗ[ℂ] M₃)
variables (e₁ : M₁ ≃ₗ* M₂) (e₂ : M₂ ≃ₗ* M₃) (e₁' : M₁ ≃ₗ[ℂ] M₂) (e₂' : M₂ ≃ₗ[ℂ] M₃)

#check g.compₛₗ f
#check g'.compₛₗ f
#check g.compₛₗ f'
#check g'.compₛₗ f'
--#check @linear_equiv.transₛₗ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ complex.cconj complex.cconj _ _
#check e₁.transₛₗ e₂
--#check e₁ trans* e₂

example (h : M₁ →ₗ[ℂ] M₃) : g.compₛₗ f = h := sorry
