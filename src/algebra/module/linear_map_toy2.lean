/-
Copyright (c) 2021 foo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: foo
-/
import algebra.group_action_hom

/-! # Fake module docstring -/

variables {R : Type*} [semiring R] {σ : R ≃+* R} {σ' : out_param (R ≃+* R)}
variables {M : Type*} {N : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid M₁] [add_comm_monoid M₂]
  [add_comm_monoid M₃]
variables [module R M] [module R N] [module R M₁] [module R M₂] [module R M₃]

/-! ### The `ring_equiv_comp_triple` typeclass hack -/
section
variables (σ₁₂ : R ≃+* R) (σ₂₃ : R ≃+* R) (σ₁₃ : out_param (R ≃+* R))

class ring_equiv_comp_triple : Prop :=
  (is_comp_triple : σ₁₃ = σ₁₂.trans σ₂₃)
variables {σ₁₂} {σ₂₃} {σ₁₃}

namespace ring_equiv_comp_triple

instance ids : ring_equiv_comp_triple (ring_equiv.refl R) σ₁₂ σ₁₂ := ⟨by { ext, simp }⟩
instance right_ids : ring_equiv_comp_triple σ₁₂ (ring_equiv.refl R) σ₁₂ := ⟨by { ext, simp }⟩

end ring_equiv_comp_triple

end


/-! ### Linear maps -/
section
set_option old_structure_cmd true
variables (R M N)

/-- A map `f` between modules over a semiring is linear if it satisfies the two properties
`f (x + y) = f x + f y` and `f (c • x) = c • f x`. -/
structure linear_map extends add_hom M N :=
(map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = (σ' r) • to_fun x)

end

notation M ` →ₛₗ[`:25 σ:25 `] `:0 N:0 := @linear_map _ _ σ M N _ _ _ _
notation M ` →ₗ[`:25 R:25 `] `:0 N:0 := @linear_map _ _ (ring_equiv.refl R) M N _ _ _ _

/-! Define composition of semilinear maps. -/
namespace linear_map

instance : has_coe_to_fun (M →ₛₗ[σ'] N) := ⟨_, to_fun⟩

variables {σ₁₂ : R ≃+* R} {σ₂₃ : R ≃+* R} {σ₁₃ : out_param (R ≃+* R)}

def comp [ring_equiv_comp_triple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
  M₁ →ₛₗ[σ₁₃] M₃ :=
{ to_fun := f ∘ g,
  map_add' := sorry,
  map_smul' := sorry }

end linear_map



/-! ### Linear equivalences -/
section
set_option old_structure_cmd true
variables (R M N)

include σ'
/-- A linear equivalence is an invertible linear map. -/
structure linear_equiv extends add_equiv M N :=
(map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = (σ' r) • to_fun x)

end

notation M ` ≃ₛₗ[`:50 σ `] ` N := @linear_equiv _ _ σ M N _ _ _ _
notation M ` ≃ₗ[`:50 R `] ` N := @linear_equiv _ _ (ring_equiv.refl R) M N _ _ _ _

/-! Define coercion -/
namespace linear_equiv

def to_linear_map (e : M ≃ₛₗ[σ'] N) : M →ₛₗ[σ'] N := { ..e }

instance has_coe : has_coe (M ≃ₛₗ[σ'] N) (M →ₛₗ[σ'] N) := ⟨to_linear_map⟩

end linear_equiv


/-! ### The elaboration issue! -/
section
variables (f₂₃ : M₂ →ₗ[R] M₃) (e₁₂ : M₁ ≃ₗ[R] M₂)

-- Ex. 1, works
example : M₁ →ₗ[R] M₂ := e₁₂

-- Ex. 2, fails, "type mismatch"
example : M₁ →ₗ[R] M₃ := f₂₃.comp e₁₂

-- Ex. 3, fails, "don't know how to synthesize placeholder `R ≃+* R`"
example : M₁ →ₗ[R] M₃ := f₂₃.comp ↑e₁₂

-- Ex. 3.5, works
example : M₁ →ₗ[R] M₃ := f₂₃.comp e₁₂.to_linear_map

-- Ex. 4, works
example : M₁ →ₗ[R] M₃ := f₂₃.comp (@has_coe.coe _ _ linear_equiv.has_coe e₁₂)

-- Ex. 5, works (as it should, this is more info than Ex. 4)
example : M₁ →ₗ[R] M₃ := f₂₃.comp (e₁₂ : M₁ →ₗ[R] M₂)

-- Ex. 6, works
example : M₁ →ₗ[R] M₃ :=
@linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ ring_equiv_comp_triple.ids f₂₃ ↑e₁₂

end
