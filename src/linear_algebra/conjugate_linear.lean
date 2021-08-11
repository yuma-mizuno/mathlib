/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import linear_algebra.basic
import data.complex.is_R_or_C

namespace is_R_or_C

variables (𝕜 : Type*) [is_R_or_C 𝕜]

/-- Complex conjugate as a ring equiv, which it probably should be in mathlib... -/
def cconj : 𝕜 ≃+* 𝕜 :=
{ to_fun := conj,
  inv_fun := conj,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  ..conj }

@[simp] lemma cconj_apply (x : 𝕜) : cconj 𝕜 x = conj x := rfl
@[simp] lemma cconj_symm_apply (x : 𝕜) : (cconj 𝕜).symm x = conj x := rfl

end is_R_or_C

namespace ring_equiv_inv_pair

variables {𝕜 : Type*} [is_R_or_C 𝕜]
instance cconj : ring_equiv_inv_pair (is_R_or_C.cconj 𝕜) (is_R_or_C.cconj 𝕜) :=
⟨ring_equiv.ext $ λ x, by simp⟩

end ring_equiv_inv_pair

--namespace ring_equiv_comp_triple
--
--instance cconj_cconj : ring_equiv_comp_triple complex.cconj complex.cconj (ring_equiv.refl ℂ) :=
--⟨ring_equiv.ext $ λ x, by simp⟩
--
--end ring_equiv_comp_triple

notation M ` →ₗ*[`:25 k:25 `] `:0 M₂:0 := linear_map (is_R_or_C.cconj k) M M₂
notation M ` ≃ₗ*[`:25 k:25 `] `:0 M₂:0 := linear_equiv (is_R_or_C.cconj k) M M₂

variables {𝕜 : Type*} [is_R_or_C 𝕜]
variables {M₁ : Type*} {M₂ : Type*} {M₃ : Type*} --{R : Type*} [semiring R]
variables [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
variables [module 𝕜 M₁] [module 𝕜 M₂] [module 𝕜 M₃] --[module R M₁] [module R M₂]
variables (f : M₁ →ₗ*[𝕜] M₂) (g : M₂ →ₗ*[𝕜] M₃) (f' : M₁ →ₗ[𝕜] M₂) (g' : M₂ →ₗ[𝕜] M₃)
--#check @linear_equiv 𝕜 𝕜 _ _ (is_R_or_C.cconj 𝕜) (is_R_or_C.cconj 𝕜) _ _ M₁ M₂ _ _ _ _
variables (e₁ : M₁ ≃ₗ*[𝕜] M₂) (e₂ : M₂ ≃ₗ*[𝕜] M₃) (e₁' : M₁ ≃ₗ[𝕜] M₂) (e₂' : M₂ ≃ₗ[𝕜] M₃)

--#check g.compₛₗ f
--#check g'.compₛₗ f
--#check g.compₛₗ f'
--#check g'.compₛₗ f'
--#check e₁.transₛₗ e₂
----#check g.compₛₗ e₁  -- fails, but also fails in std mathlib
--#check g'.comp (e₁' : M₁ →ₗ[𝕜] M₂)
--#check g'.comp ↑e₁'
--#check g'.compₛₗ ↑e₁'
--#check g.compₛₗ (e₁ : M₁ →ₗ*[𝕜] M₂)
--#check g.compₛₗ (e₁' : M₁ →ₗ[𝕜] M₂)
--#check g'.compₛₗ (e₁' : M₁ →ₗ[𝕜] M₂)
--#check g'.compₛₗ (e₁ : M₁ →ₗ*[𝕜] M₂)
--#check g'.compₛₗ (e₁ : M₁ →ₗ*[𝕜] M₂)
--
--#check e₁.symm
--#check e₁'.symm
--#check e₁'.symm.transₛₗ e₁
--#check e₁.symm.transₛₗ e₁'
--#check e₁.transₛₗ e₁.symm
--#check e₁.transₛₗ e₁'.symm
--#check e₁'.transₛₗ e₁'.symm
--#check e₁'.transₛₗ e₁.symm
