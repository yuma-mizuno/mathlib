/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.noetherian
import algebra.category.Module.monoidal
import category_theory.adjunction.limits

universe variables u

variables {R : Type u} {M N P Q : Type*} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]
variables [add_comm_group Q] [module R Q]

section move_this

open category_theory
open category_theory.limits
open category_theory.monoidal_category

instance (M : Module.{u} R) : preserves_colimits (tensor_right M) :=
adjunction.left_adjoint_preserves_colimits is_left_adjoint.adj

end move_this

open_locale tensor_product

-- move this
namespace linear_map

lemma injective_iff (f : M →ₗ[R] N) : function.injective f ↔ ∀ m, f m = 0 → m = 0 :=
add_monoid_hom.injective_iff f.to_add_monoid_hom

variables (M)

/-- `ltensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map induced by `f : N →ₗ P`. -/
def ltensor (f : N →ₗ[R] P) : M ⊗ N →ₗ[R] M ⊗ P :=
tensor_product.map id f

/-- `rtensor f M : N₁ ⊗ M →ₗ N₂ ⊗ M` is the natural linear map induced by `f : N₁ →ₗ N₂`. -/
def rtensor (f : N →ₗ[R] P) (M : Type*) [add_comm_group M] [module R M] :
  N ⊗ M →ₗ[R] P ⊗ M :=
tensor_product.map f id

variables (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

@[simp] lemma ltensor_tmul (m : M) (n : N) : f.ltensor M (m ⊗ₜ n) = m ⊗ₜ (f n) := rfl

@[simp] lemma rtensor_tmul (m : M) (n : N) : f.rtensor M (n ⊗ₜ m) = (f n) ⊗ₜ m := rfl

lemma ltensor_comp : (g.comp f).ltensor M = (g.ltensor M).comp (f.ltensor M) :=
by { ext m n, simp only [comp_apply, ltensor_tmul] }

lemma rtensor_comp : (g.comp f).rtensor M = (g.rtensor M).comp (f.rtensor M) :=
by { ext m n, simp only [comp_apply, rtensor_tmul] }

variables (N)

@[simp] lemma ltensor_id : (id : N →ₗ[R] N).ltensor M = id :=
by { ext m n, simp only [id_coe, id.def, ltensor_tmul] }

@[simp] lemma rtensor_id : (id : N →ₗ[R] N).rtensor M = id :=
by { ext m n, simp only [id_coe, id.def, rtensor_tmul] }

end linear_map

namespace submodule

variables {R M}

lemma supr_span_eq_self (N : submodule R M) :
  (⨆ x ∈ N, span R {x}) = N :=
begin
  apply le_antisymm,
  { simp only [supr_le_iff],
    intros x hx,
    rwa [span_singleton_le_iff_mem] },
  { intros x hx,
    rw mem_supr,
    intros P hP,
    refine hP x _,
    rw mem_supr,
    intros Q hQ,
    refine hQ hx _,
    exact mem_span_singleton_self x }
end

lemma supr_le_fg_eq_self (N : submodule R M) :
  (⨆ (P : submodule R M) (hPN : P ≤ N) (hP : P.fg), P) = N :=
begin
  apply le_antisymm,
  { iterate 3 { refine supr_le _, intro }, assumption },
  { intros x hx,
    suffices : span R {x} ≤ (⨆ (P : submodule R M) (hPN : P ≤ N) (hP : P.fg), P),
    { exact this (mem_span_singleton_self x) },
    simp only [le_supr_iff, supr_le_iff],
    intros P hP,
    apply hP,
    { rwa [span_le, set.singleton_subset_iff] },
    { refine ⟨{x}, _⟩, simp only [finset.coe_singleton] } }
end

def incl {N P : submodule R M} (h : N ≤ P) : N →ₗ[R] P :=
{ to_fun := set.inclusion h,
  map_add' := λ x y, rfl,
  map_smul' := λ c x, rfl }

end submodule

namespace ideal

variables {R}

lemma supr_span_eq_self (I : ideal R) :
  (⨆ r ∈ I, span {r}) = I :=
submodule.supr_span_eq_self I

lemma supr_le_fg_eq_self (I : ideal R) :
  (⨆ (J : ideal R) (hJI : J ≤ I) (hJ : J.fg), J) = I :=
submodule.supr_le_fg_eq_self I

end ideal

namespace module
open function (injective)
open linear_map (lsmul)

open_locale tensor_product

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the map `I ⊗ M →ₗ M` is injective. -/
def flat (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] : Prop :=
∀ ⦃I : ideal R⦄ (hI : I.fg),
  injective (show I ⊗[R] M →ₗ[R] M, from tensor_product.lift ((lsmul R M).comp I.subtype))

namespace flat

lemma injective_lsmul_comp_subtype (hM : flat R M) (I : ideal R) :
  injective (show I ⊗[R] M →ₗ[R] M, from tensor_product.lift ((lsmul R M).comp I.subtype)) :=
begin
  rw linear_map.injective_iff,
  intros x hx,
  sorry
end

lemma injective_ltensor (hM : flat R M) (f : N →ₗ[R] P) (hf : injective f) :
  injective (f.ltensor M) :=
begin
  sorry
end

end flat

lemma flat_iff_ltensor_injective :
  flat R M ↔ ∀ (f : N →ₗ[R] P) (hf : injective f), injective (f.ltensor M) :=
begin
  sorry
end

end module
