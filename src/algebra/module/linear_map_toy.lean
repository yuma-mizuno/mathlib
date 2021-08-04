/-
Copyright (c) 2021 foo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: foo
-/

/-! # Fake module docstring -/


/-- Copy of mathlib's `has_scalar` to avoid big imports -/
class has_scalar (M : Type*) (α : Type*) := (smul : M → α → α)

infixr ` • `:73 := has_scalar.smul


variables {R : Type*} {S : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variables {σ : R → S}
variables {M : Type*} {N : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variables [has_scalar R M] [has_scalar S N]

/-! ### The `ring_equiv_comp_triple` typeclass hack -/
section
variables (σ₁₂ : R₁ → R₂) (σ₂₃ : R₂ → R₃) (σ₁₃ : out_param (R₁ → R₃))

class ring_equiv_comp_triple : Prop :=
  (is_comp_triple : σ₁₃ = σ₂₃ ∘ σ₁₂)
variables {σ₁₂} {σ₂₃} {σ₁₃}

namespace ring_equiv_comp_triple

instance ids : ring_equiv_comp_triple (id : R₁ → R₁) σ₁₂ σ₁₂ := ⟨sorry⟩
instance right_ids : ring_equiv_comp_triple σ₁₂ (id : R₂ → R₂) σ₁₂ := ⟨sorry⟩

end ring_equiv_comp_triple

end


/-! ### Linear maps -/
section
set_option old_structure_cmd true
variables (σ M N)

/-- A map `f` between types with scalar actions is `σ`-linear if it satisfies the property
`f (c • x) = σ c • f x`. -/
structure linear_map :=
(to_fun : M → N)
(map_smul' : ∀ (r : R) (x : M), to_fun (r • x) = (σ r) • to_fun x)

end

notation M ` →ₛₗ[`:25 σ:25 `] `:0 N:0 := linear_map σ M N
notation M ` →ₗ[`:25 R:25 `] `:0 N:0 := linear_map (id : R → R) M N

/-! Define composition of semilinear maps. -/
namespace linear_map

variables [has_scalar R₁ M₁] [has_scalar R₂ M₂] [has_scalar R₃ M₃]
variables {σ₁₂ : R₁ → R₂} {σ₂₃ : R₂ → R₃} {σ₁₃ : out_param (R₁ → R₃)}

def comp [ring_equiv_comp_triple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :
  M₁ →ₛₗ[σ₁₃] M₃ :=
{ to_fun := f.to_fun ∘ g.to_fun,
  map_smul' := sorry }

end linear_map



/-! ### Linear equivalences -/
section
set_option old_structure_cmd true
variables (σ M N)

/-- A linear equivalence is a structure extending `linear_map`. -/
structure linear_equiv extends linear_map σ M N

end

notation M ` ≃ₛₗ[`:50 σ `] ` N := linear_equiv σ M N
notation M ` ≃ₗ[`:50 R `] ` N := linear_equiv (id : R → R) M N

/-! Define coercion -/
instance linear_equiv.has_coe : has_coe (M ≃ₛₗ[σ] N) (M →ₛₗ[σ] N) := ⟨linear_equiv.to_linear_map⟩


/-! ### The elaboration issue! -/
section
variables [has_scalar R M₁] [has_scalar R M₂] [has_scalar R M₃]
variables (f₂₃ : M₂ →ₗ[R] M₃) (e₁₂ : M₁ ≃ₗ[R] M₂)

-- Ex. 1, works
example : M₁ →ₗ[R] M₂ := e₁₂

-- Ex. 2, fails, "type mismatch"
example : M₁ →ₗ[R] M₃ := f₂₃.comp e₁₂

-- Ex. 3, fails, "don't know how to synthesize placeholder `R → R`"
example : M₁ →ₗ[R] M₃ := f₂₃.comp ↑e₁₂

-- Ex. 3.5, works
example : M₁ →ₗ[R] M₃ := f₂₃.comp e₁₂.to_linear_map

-- Ex. 4, works
example : M₁ →ₗ[R] M₃ := f₂₃.comp (@has_coe.coe _ _ linear_equiv.has_coe e₁₂)

-- Ex. 5, works (as it should, this is more info than Ex. 4)
example : M₁ →ₗ[R] M₃ := f₂₃.comp (e₁₂ : M₁ →ₗ[R] M₂)

-- Ex. 6, works
example : M₁ →ₗ[R] M₃ :=
@linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ ring_equiv_comp_triple.ids f₂₃ ↑e₁₂

end
