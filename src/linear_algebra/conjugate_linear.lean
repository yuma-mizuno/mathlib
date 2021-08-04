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

end ring_equiv_inv_pair

--namespace ring_equiv_comp_triple
--
--instance cconj_cconj : ring_equiv_comp_triple complex.cconj complex.cconj (ring_equiv.refl ℂ) :=
--⟨ring_equiv.ext $ λ x, by simp⟩
--
--end ring_equiv_comp_triple

notation M ` →ₗ* ` M₂:0 := linear_map complex.cconj M M₂

variables {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module ℂ M₁] [module ℂ M₂] [module ℂ M₃]
variables (f : M₁ →ₗ* M₂) (g : M₂ →ₗ* M₃)

#check g
#check f
#check g.compₛₗ f

example (h : M₁ →ₗ[ℂ] M₃) : g.compₛₗ f = h := sorry
