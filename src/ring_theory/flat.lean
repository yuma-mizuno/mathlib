/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import linear_algebra.dimension
import ring_theory.noetherian
import algebra.category.Module.monoidal
import category_theory.adjunction.limits
import ring_theory.algebra_tower
import tactic.apply_fun
import tactic

/-!
## Inspiration/contributors

Contributions by Roman Fedorov
-/

universe variables u

variables {R : Type u} {M N P Q : Type*} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]
variables [add_comm_group Q] [module R Q]

section move_this

/-- Scalar multiplication gives a linear map. Probably belongs to linear_algebra.tensor_product.-/
def linear_map_smul (P : Type u) [add_comm_group P] [module R P] (r : R) : P →ₗ[R] P :=
{to_fun := (λ (x : P), r • x),
map_add' := (is_linear_map.is_linear_map_smul r).map_add,
map_smul' := (is_linear_map.is_linear_map_smul r).map_smul}

@[simp] lemma equiv.injective_comp {α β γ : Type*} (e : α ≃ β) (f : β → γ) :
  function.injective (f ∘ e) ↔ function.injective f :=
begin
  split,
  { intros h x y hxy,
    apply e.symm.injective,
    apply h,
    simp only [hxy, function.comp_app, equiv.apply_symm_apply] },
  { intro h, exact h.comp e.injective }
end

@[simp] lemma equiv.comp_injective {α β γ : Type*} (f : α → β) (e : β ≃ γ) :
  function.injective (e ∘ f) ↔ function.injective f :=
begin
  refine ⟨_, e.injective.comp⟩,
  intros h x y hxy,
  apply h,
  apply e.symm.injective,
  simp only [hxy, function.comp_app, equiv.apply_symm_apply]
end

open category_theory
open category_theory.limits
open category_theory.monoidal_category

instance (M : Module.{u} R) : preserves_colimits (tensor_right M) :=
adjunction.left_adjoint_preserves_colimits is_left_adjoint.adj

end move_this

open_locale tensor_product


-- move this
namespace linear_map

lemma one_def : (1 : M →ₗ[R] M) = id := rfl

lemma mul_def (g f : M →ₗ[R] M) : g * f = g.comp f := rfl

lemma injective_iff (f : M →ₗ[R] N) : function.injective f ↔ ∀ m, f m = 0 → m = 0 :=
add_monoid_hom.injective_iff f.to_add_monoid_hom

variables (M)

/-- `ltensor M f : M ⊗ N →ₗ M ⊗ P` is the natural linear map induced by `f : N →ₗ P`. -/
def ltensor (f : N →ₗ[R] P) : M ⊗ N →ₗ[R] M ⊗ P :=
tensor_product.map id f

lemma tensor_left_map (M : Module.{u} R) {N P : Module.{u} R} (f : N ⟶ P) :
  (category_theory.monoidal_category.tensor_left M).map f = f.ltensor M := rfl

/-- `rtensor f M : N₁ ⊗ M →ₗ N₂ ⊗ M` is the natural linear map induced by `f : N₁ →ₗ N₂`. -/
def rtensor (f : N →ₗ[R] P) :
  N ⊗ M →ₗ[R] P ⊗ M :=
tensor_product.map f id

lemma tensor_right_map (M : Module.{u} R) {N P : Module.{u} R} (f : N ⟶ P) :
  (category_theory.monoidal_category.tensor_right M).map f = f.rtensor M := rfl

variables (g : P →ₗ[R] Q) (f : N →ₗ[R] P)

@[simp] lemma ltensor_tmul (m : M) (n : N) : f.ltensor M (m ⊗ₜ n) = m ⊗ₜ (f n) := rfl

@[simp] lemma rtensor_tmul (m : M) (n : N) : f.rtensor M (n ⊗ₜ m) = (f n) ⊗ₜ m := rfl

open tensor_product

/-- `ltensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def ltensor_hom : (N →ₗ[R] P) →ₗ[R] (M ⊗[R] N →ₗ[R] M ⊗[R] P) :=
{ to_fun := ltensor M,
  map_add' := λ f g, by { ext x y, simp only [add_apply, ltensor_tmul, tmul_add] },
  map_smul' := λ r f, by { ext x y, simp only [tmul_smul, smul_apply, ltensor_tmul] } }

@[simp] lemma coe_ltensor_hom :
  (ltensor_hom M : (N →ₗ[R] P) → (M ⊗[R] N →ₗ[R] M ⊗[R] P)) = ltensor M := rfl

@[simp] lemma ltensor_add (f g : N →ₗ[R] P) : (f + g).ltensor M = f.ltensor M + g.ltensor M :=
(ltensor_hom M).map_add f g

@[simp] lemma ltensor_sub (f g : N →ₗ[R] P) : (f - g).ltensor M = f.ltensor M - g.ltensor M :=
by simp only [← coe_ltensor_hom, map_sub]

@[simp] lemma ltensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).ltensor M = r • (f.ltensor M) :=
(ltensor_hom M).map_smul r f

@[simp] lemma ltensor_neg (f : N →ₗ[R] P) : (-f).ltensor M = -(f.ltensor M) :=
by simp only [← coe_ltensor_hom, map_neg]

@[simp] lemma ltensor_zero : ltensor M (0 : N →ₗ[R] P) = 0 :=
(ltensor_hom M).map_zero

/-- `rtensor_hom M` is the natural linear map that sends a linear map `f : N →ₗ P` to `M ⊗ f`. -/
def rtensor_hom : (N →ₗ[R] P) →ₗ[R] (N ⊗[R] M →ₗ[R] P ⊗[R] M) :=
{ to_fun := λ f, f.rtensor M,
  map_add' := λ f g, by { ext x y, simp only [add_apply, rtensor_tmul, add_tmul] },
  map_smul' := λ r f, by { ext x y, simp only [smul_tmul, tmul_smul, smul_apply, rtensor_tmul] } }

@[simp] lemma coe_rtensor_hom :
  (rtensor_hom M : (N →ₗ[R] P) → (N ⊗[R] M →ₗ[R] P ⊗[R] M)) = rtensor M := rfl

@[simp] lemma rtensor_add (f g : N →ₗ[R] P) : (f + g).rtensor M = f.rtensor M + g.rtensor M :=
(rtensor_hom M).map_add f g

@[simp] lemma rtensor_sub (f g : N →ₗ[R] P) : (f - g).rtensor M = f.rtensor M - g.rtensor M :=
by simp only [← coe_rtensor_hom, map_sub]

@[simp] lemma rtensor_smul (r : R) (f : N →ₗ[R] P) : (r • f).rtensor M = r • (f.rtensor M) :=
(rtensor_hom M).map_smul r f

@[simp] lemma rtensor_neg (f : N →ₗ[R] P) : (-f).rtensor M = -(f.rtensor M) :=
by simp only [← coe_rtensor_hom, map_neg]

@[simp] lemma rtensor_zero : rtensor M (0 : N →ₗ[R] P) = 0 :=
(rtensor_hom M).map_zero

lemma ltensor_comp : (g.comp f).ltensor M = (g.ltensor M).comp (f.ltensor M) :=
by { ext m n, simp only [comp_apply, ltensor_tmul] }

lemma rtensor_comp : (g.comp f).rtensor M = (g.rtensor M).comp (f.rtensor M) :=
by { ext m n, simp only [comp_apply, rtensor_tmul] }

variables (N)

@[simp] lemma ltensor_id : (id : N →ₗ[R] N).ltensor M = id :=
by { ext m n, simp only [id_coe, id.def, ltensor_tmul] }

@[simp] lemma rtensor_id : (id : N →ₗ[R] N).rtensor M = id :=
by { ext m n, simp only [id_coe, id.def, rtensor_tmul] }

variables {N}

variables {M' : Type*}
variables [add_comm_group M'] [module R M']

open tensor_product

@[simp] lemma ltensor_comp_rtensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (g.ltensor P).comp (f.rtensor N) = map f g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma rtensor_comp_ltensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (f.rtensor Q).comp (g.ltensor M) = map f g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma map_comp_rtensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (f' : M' →ₗ[R] M) :
  (map f g).comp (f'.rtensor _) = map (f.comp f') g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma map_comp_ltensor (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (g' : M' →ₗ[R] N) :
  (map f g).comp (g'.ltensor _) = map f (g.comp g') :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma rtensor_comp_map (f' : P →ₗ[R] M') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (f'.rtensor _).comp (map f g) = map (f'.comp f) g :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

@[simp] lemma ltensor_comp_map (g' : Q →ₗ[R] M') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (g'.ltensor _).comp (map f g) = map f (g'.comp g) :=
by simp only [ltensor, rtensor, ← map_comp, id_comp, comp_id]

/-- The isomorphism M ⊗[R] R ≃ₗ M is functorial in M.
Probably belongs to linear_algebra.tensor_product. -/

theorem tensor_product_rid_functorial (f : M →ₗ[R] N) :
  (tensor_product.rid R N : N ⊗[R] R ≃ₗ N) ∘ (rtensor R f : (M ⊗[R] R) →ₗ[R] (N ⊗[R] R)) =
  f ∘ (tensor_product.rid R M : M ⊗[R] R ≃ₗ M) :=
let g₁ : M ⊗[R] R ≃ₗ M := tensor_product.rid R M in
let g₂ : N ⊗[R] R ≃ₗ N := tensor_product.rid R N in
have h_compose : (g₂.to_linear_map.comp (rtensor R f) = f.comp g₁.to_linear_map), by
{
  apply tensor_product.ext,
  intros m r,
  repeat{rw [comp_apply]},
  exact calc
  g₂.to_linear_map (rtensor R f (m ⊗ₜ[R] r)) = (g₂.to_linear_map) ((f m) ⊗ₜ[R] (linear_map.id r)) :
    by refl
    ... = (tensor_product.rid R N) ((f m) ⊗ₜ[R] r) : rfl
    ... = r • f m                                  : by rw [tensor_product.rid_tmul (f m) r]
    ... = f (r • m)                                : (f.map_smul r m).symm
    ... = f ((tensor_product.rid R M) (m ⊗ₜ[R] r)) : by rw [tensor_product.rid_tmul m r]
    ... = f (g₁.to_linear_map (m ⊗ₜ[R] r))          : rfl
},
by
{
  apply funext,
  exact (ext_iff.1 h_compose)
}

/-- RF: The associator for tensor product is functorial in the third argument.
Probably belongs to linear_algebra.tensor_product.-/

variable {M}
lemma assoc_functorial_third (f : M →ₗ[R] N) :
let α := tensor_product.assoc R P Q M in let β := tensor_product.assoc R P Q N in
  (ltensor P (ltensor Q f)).comp  α.to_linear_map  = β.to_linear_map.comp (ltensor (P ⊗ Q) f) :=
let ftt : (P ⊗[R] (Q ⊗[R] M)) →ₗ[R](P ⊗[R] (Q ⊗[R] N)) := ltensor P (ltensor Q f) in
let ftt': ((P ⊗[R] Q) ⊗[R] M) →ₗ[R]((P ⊗[R] Q) ⊗[R] N) := ltensor (P ⊗ Q) f in
let α := tensor_product.assoc R P Q M in let β := tensor_product.assoc R P Q N in
  ext_threefold (assume (p : P) (q : Q) (m : M),
  have heq₁  : (ftt.comp α.to_linear_map) ((p ⊗ₜ q) ⊗ₜ m) = (p ⊗ₜ (q ⊗ₜ f m)),
  from calc
    (comp ftt α.to_linear_map) ((p ⊗ₜ q) ⊗ₜ m) = ftt (α.to_linear_map ((p ⊗ₜ q) ⊗ₜ m)) :
      comp_apply _ _ _
    ... = ftt (p ⊗ₜ (q ⊗ₜ m)) : by refl
    ... = (linear_map.id p) ⊗ₜ (ltensor Q f) (q ⊗ₜ m) : map_tmul _ _ _ _
    ... = p ⊗ₜ (ltensor Q f) (q ⊗ₜ m)                 : by rw [id_apply]
    ... = p ⊗ₜ (q ⊗ₜ f m)                  : by rw[ltensor_tmul],
  have heq₂ : (comp β.to_linear_map ftt') ((p ⊗ₜ q) ⊗ₜ m) = (p ⊗ₜ (q ⊗ₜ f m)), from calc
    (comp β.to_linear_map ftt') ((p ⊗ₜ q) ⊗ₜ m) = β.to_linear_map (ftt' ((p ⊗ₜ q) ⊗ₜ m)) :
        comp_apply _ _ _
    ... = β.to_linear_map ((p ⊗ₜ q) ⊗ₜ f m)                 : by rw[ltensor_tmul]
    ... = (p ⊗ₜ (q ⊗ₜ f m))                                 : by refl,
  heq₁.trans heq₂)
variable (M)

end linear_map

namespace module
open linear_map (hiding restrict_scalars)

variables (A B : Type*) [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
variables [module A N] [is_scalar_tower R A N]

instance algebra_tensor_module : module A (A ⊗[R] M) :=
{ smul := λ a, rtensor M (algebra.lmul R A a),
  one_smul := λ x, by simp only [alg_hom.map_one, one_def, id.def, id_coe, rtensor_id],
  mul_smul := λ a b x, by simp only [alg_hom.map_mul, mul_def, rtensor_comp, comp_apply],
  smul_add := λ a x y, by simp only [map_add],
  smul_zero := λ a, by simp only [map_zero],
  add_smul := λ a b x, by simp only [alg_hom.map_add, add_apply, rtensor_add],
  zero_smul := λ x, by simp only [rtensor_zero, alg_hom.map_zero, zero_apply] }

instance algebra_tensor_module_is_scalar_tower :
  is_scalar_tower R A (A ⊗[R] M) :=
_

instance hom_module_over_algebra : module A (M →ₗ[R] N) :=
{ smul := λ a, linear_map.comp (a • @linear_map.id A N _ _ _),
  one_smul := λ x, by simp only [one_def, algebra.lmul_right_one, comp_id],
  mul_smul := λ a b x, by simp only [comp_assoc, algebra.lmul_right_mul],
  smul_add := λ a x y, by simp only [add_comp],
  smul_zero := λ a, by simp only [zero_comp],
  add_smul := λ a b x, by simp only [comp_add, algebra.lmul_right, map_add],
  zero_smul := λ x, by simp only [comp_zero, algebra.lmul_right, map_zero] }

instance hom_module_over_algebra_is_scalar_tower :
  is_scalar_tower R A (M →ₗ[R] N) :=
_


-- reorder and rename variables
def uncurry' :
  (A ⊗[R] M →ₗ[A] N) →ₗ[A] M →ₗ[R] N :=
_

-- reorder and rename variables
def tensor_product.assoc' (N : Type*) [add_comm_group N] [module A N] :
  restrict_scalars R A (N ⊗[A] A) ⊗[R] M ≃ₗ[R] restrict_scalars R A (N ⊗[A] (A ⊗[R] M)) :=
{ to_fun := _,
  inv_fun := _,
  map_add' := _,
  map_smul' := _,
  left_inv := _,
  right_inv := _ }

def tensor_product.contract : B ⊗[A] (A ⊗[R] M) ≃ₗ[B] B ⊗[R] M :=
{ to_fun := _,
  map_smul' := _,
  .. (show restrict_scalars R A (B ⊗[A] (A ⊗[R] M)) ≃ₗ[R] B ⊗[R] M,
      from sorry) }

end module

namespace linear_map
open tensor_product

variables (A B : Type*) [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]
variables (f g : M →ₗ[R] N)

/-- `base_change A f` for `f : M →ₗ[R] N` is the `A`-linear map `A ⊗[R] M →ₗ[A] A ⊗[R] N`. -/
def base_change (f : M →ₗ[R] N) : A ⊗[R] M →ₗ[A] A ⊗[R] N :=
{ to_fun := f.ltensor A,
  map_add' := (f.ltensor A).map_add,
  map_smul' := λ a x,
    show (f.ltensor A) (rtensor M (algebra.lmul R A a) x) =
      (rtensor N ((algebra.lmul R A) a)) ((ltensor A f) x),
    by simp only [← comp_apply, ltensor_comp_rtensor, rtensor_comp_ltensor] }

@[simp] lemma base_change_tmul (a : A) (x : M) :
  f.base_change A (a ⊗ₜ x) = a ⊗ₜ (f x) := rfl

lemma base_change_eq_ltensor :
  (f.base_change A : A ⊗ M → A ⊗ N) = f.ltensor A := rfl

@[simp] lemma base_change_add :
  (f + g).base_change A = f.base_change A + g.base_change A :=
by { ext, simp only [base_change_eq_ltensor, add_apply, ltensor_add] }

@[simp] lemma base_change_sub :
  (f - g).base_change A = f.base_change A - g.base_change A :=
by { ext, simp only [base_change_eq_ltensor, sub_apply, ltensor_sub] }

-- @[simp] lemma base_change_smul (r : R) :
--   (r • f).base_change A = r • (f.base_change A) :=
-- sorry

@[simp] lemma base_change_neg : (-f).base_change A = -(f.base_change A) :=
by { ext, simp only [base_change_eq_ltensor, neg_apply, ltensor_neg] }

@[simp] lemma base_change_zero : base_change A (0 : M →ₗ[R] N) = 0 :=
by { ext, simp only [base_change_eq_ltensor, zero_apply, ltensor_zero] }

@[simp] lemma base_change_base_change :
  (f.base_change A).base_change B = (linear_map.comp _ (f.base_change B)).comp _ :=
begin

end

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

def to_map (P : submodule R M) (f : M →ₗ[R] N) : P →ₗ[R] (P.map f) :=
(f.dom_restrict P).cod_restrict _ $ λ x, ⟨x, x.2, rfl⟩

lemma fg_span_of_finite (s : set M) (hs : s.finite) :
  (span R s).fg :=
⟨hs.to_finset, by rw [set.finite.coe_to_finset]⟩

@[simp] lemma fg_span_singleton (x : M) : (span R ({x} : set M)).fg :=
⟨{x}, by simp only [finset.coe_singleton]⟩

lemma exists_fg_tmul_mem_range (x : M ⊗[R] N) :
  ∃ (P : submodule R M) (Q : submodule R N) (hP : P.fg) (hQ : Q.fg),
  x ∈ (tensor_product.map P.subtype Q.subtype).range :=
begin
  apply tensor_product.induction_on x; clear x,
  { exact ⟨⊥, ⊥, fg_bot, fg_bot, submodule.zero_mem _⟩ },
  { intros x y,
    refine ⟨span R {x}, span R {y}, fg_span_singleton x, fg_span_singleton y, _⟩,
    refine ⟨⟨x, mem_span_singleton_self x⟩ ⊗ₜ ⟨y, mem_span_singleton_self y⟩, _⟩,
    simp only [subtype_apply, coe_mk, top_coe, set.mem_univ, eq_self_iff_true, and_self,
      tensor_product.map_tmul] },
  { rintro x y ⟨Px, Qx, hPx, hQx, x, -, rfl⟩ ⟨Py, Qy, hPy, hQy, y, -, rfl⟩,
    refine ⟨Px ⊔ Py, Qx ⊔ Qy, fg_sup hPx hPy, fg_sup hQx hQy, _⟩,
    refine ⟨tensor_product.map (incl (@le_sup_left  _ _ Px Py)) (incl (@le_sup_left  _ _ Qx Qy)) x +
            tensor_product.map (incl (@le_sup_right _ _ Px Py)) (incl (@le_sup_right _ _ Qx Qy)) y,
            trivial, _⟩,
    simp only [linear_map.map_add, ← linear_map.comp_apply, ← tensor_product.map_comp],
    refl }
end

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
@[class]
def flat (R M : Type*) [comm_ring R] [add_comm_group M] [module R M] : Prop :=
∀ ⦃I : ideal R⦄ (hI : I.fg),
  injective (show I ⊗[R] M →ₗ[R] M, from tensor_product.lift ((lsmul R M).comp I.subtype))

namespace flat

open submodule linear_map

variables (M)

lemma injective_lsmul_comp_subtype [hM : flat R M] (I : ideal R) :
  injective (show I ⊗[R] M →ₗ[R] M, from tensor_product.lift ((lsmul R M).comp I.subtype)) :=
begin
  rw injective_iff,
  intros x hx,
  obtain ⟨J', N, hJ', hN, x, ⟨-, rfl⟩⟩ := exists_fg_tmul_mem_range x,
  let J : ideal R := J'.map I.subtype,
  have hJ : J.fg := fg_map hJ',
  let x' : J ⊗[R] M := tensor_product.map (J'.to_map I.subtype) N.subtype x,
  let ι : J →ₗ[R] I := incl (λ x, by { rw mem_map, rintro ⟨⟨x, hx⟩, -, rfl⟩, exact hx }),
  have hι : ι.comp (J'.to_map I.subtype) = J'.subtype,
  { ext, refl },
  specialize hM hJ,
  rw injective_iff at hM,
  specialize hM x' (by simpa only [x', ← hι, ← comp_apply, tensor_product.lift_comp_map] using hx),
  apply_fun ι.rtensor M at hM,
  simpa only [linear_map.map_zero, x', ← comp_apply, rtensor_comp_map, hι] using hM
end
.

variable {n : ℕ}

set_option profiler true
-- set_option class.instance_max_depth 32
-- set_option trace.class_instances true

#check (by apply_instance : module R (fin n → R))

lemma injective_rtensor_aux₁ [hM : flat R M] {n : ℕ} (L : submodule R (fin n → R)) :
  injective (L.subtype.rtensor M) :=
begin
  -- refine (injective_iff _).mpr _,
  -- rw [show M = M, from rfl],
  rw injective_iff,
  -- induction n with n IH,
  { sorry },
end

-- RF #exit

lemma injective_rtensor_aux₂ [flat R M] {n : ℕ} {P Q : submodule R N}
  (hP : P.fg) (hQ : Q.fg) (h : P ≤ Q) :
  injective ((incl h).rtensor M) :=
begin
  have := finsupp.total,
  -- rw injective_iff,
  -- induction n with n IH,
  { sorry },
end

lemma rtensor_injective [flat R M] (f : N →ₗ[R] P) (hf : injective f) :
  injective (f.rtensor M) :=
begin
  rw injective_iff,
  intros x hx,
  obtain ⟨p, q, hp, hq, x, ⟨-, rfl⟩⟩ := exists_fg_tmul_mem_range x,
  rw [← comp_apply, rtensor_comp_map] at hx,
  let x' : p ⊗ M := q.subtype.ltensor p x,
  rw [← rtensor_comp_ltensor, comp_apply] at hx ⊢,
end

lemma rtensor_injective_iff_ltensor_injective (f : N →ₗ[R] P) :
  injective (f.rtensor M) ↔ injective (f.ltensor M) :=
begin
  suffices : ltensor M f = (linear_map.comp (↑(tensor_product.comm R P M) : P ⊗[R] M →ₗ[R] M ⊗ P)
    (f.rtensor M)).comp (tensor_product.comm R M N),
  { rw this,
    simp only [←comp_coe, linear_equiv.coe_coe, ← linear_equiv.coe_to_equiv,
      equiv.injective_comp, equiv.comp_injective] },
  ext x y,
  simp only [comp_apply, rtensor_tmul, linear_equiv.coe_coe, ltensor_tmul, tensor_product.comm_tmul]
end

lemma ltensor_injective [flat R M] (f : N →ₗ[R] P) (hf : injective f) :
  injective (f.ltensor M) :=
begin
  rw ← rtensor_injective_iff_ltensor_injective,
  exact rtensor_injective _ f hf
end

variables (A : Type*) [comm_ring A] [algebra R A]

lemma base_change_injective [flat R A] (f : N →ₗ[R] P) (hf : injective f) :
  injective (f.base_change A) :=
ltensor_injective A f hf

open tensor_product

instance self : flat R R :=
begin
  intros I hI,
  rw ← equiv.injective_comp (tensor_product.rid R I).symm.to_equiv,
  convert subtype.coe_injective using 1,
  ext x,
  simp only [function.comp_app, linear_equiv.coe_to_equiv, rid_symm_apply, comp_apply,
    mul_one, lift.tmul, subtype_apply, algebra.id.smul_eq_mul, lsmul_apply]
end

end flat

lemma flat_iff_rtensor_injective :
  flat R M ↔
  ∀ ⦃N P : Type u⦄ [add_comm_group N] [add_comm_group P],
    by exactI ∀ [module R N] [module R P],
    by exactI ∀ (f : N →ₗ[R] P) (hf : injective f), injective (f.rtensor M) :=
begin
  split,
  { introsI hM N P _ _ _ _ f hf,
    exact @flat.rtensor_injective R M N P _ _ _ _ _ _ _ hM f hf },
  intros hM I hI,
  specialize hM I.subtype subtype.coe_injective,
  suffices : tensor_product.lift ((lsmul R M).comp (submodule.subtype I)) =
    linear_map.comp ↑(tensor_product.lid R M) ((submodule.subtype I).rtensor M),
  { rw this, exact function.injective.comp (tensor_product.lid R M).injective hM },
  ext1 x,
  simp only [tensor_product.lift.tmul, linear_equiv.coe_coe, tensor_product.lid_tmul,
    linear_map.rtensor_tmul, linear_map.lsmul_apply, linear_map.comp_apply]
end

-- RF
lemma flat_iff_ltensor_injective :
  flat R M ↔
  ∀ ⦃N P : Type u⦄ [add_comm_group N] [add_comm_group P],
    by exactI ∀ [module R N] [module R P],
    by exactI ∀ (f : N →ₗ[R] P) (hf : injective f), injective (f.ltensor M) :=
 begin
   split,
     {introsI, apply flat.ltensor_injective, assumption},
     {introsI hFM, apply flat_iff_rtensor_injective.2, introsI,
     apply (flat.rtensor_injective_iff_ltensor_injective M f).2,
     exact hFM f hf}
 end

open linear_map (ltensor) (rtensor) (assoc_functorial_third) (comp_apply)
(tensor_product_rid_functorial) -- RF

/-- RF: The tensor product of flat modules is flat -/

lemma tensor_product_flat {P : Type u} [add_comm_group P] [module R P] (hFP : flat R P)
{Q : Type u} [add_comm_group Q] [module R Q] (hFQ: flat R Q) : flat R (P⊗[R] Q) :=
begin
apply flat_iff_ltensor_injective.2, introsI M N _ _ _ _ f inj,
exact
let ft : (Q ⊗[R] M) →ₗ[R] (Q ⊗[R] N) := ltensor Q f in
have injt : function.injective ft, from flat_iff_ltensor_injective.1 hFQ f inj,
let ftt : (P ⊗[R] (Q ⊗[R] M)) →ₗ[R](P ⊗[R] (Q ⊗[R] N)) := ltensor P ft in
have injt : function.injective ftt, from flat_iff_ltensor_injective.1 hFP ft injt,
let ftt': ((P ⊗[R] Q) ⊗[R] M) →ₗ[R]((P ⊗[R] Q) ⊗[R] N) := ltensor (P ⊗ Q) f in
let h₁ := tensor_product.assoc R P Q M in let h₂ := tensor_product.assoc R P Q N in
have Comm : ftt.comp (h₁.to_linear_map) = (h₂.to_linear_map).comp ftt',
from assoc_functorial_third f,
have Comm': ftt ∘ h₁ = h₂ ∘ ftt', by {funext, exact
(calc
  (ftt ∘ h₁) x = ftt (h₁ x) : rfl
  ... =  (ftt.comp (h₁.to_linear_map)) x :  by {rw[comp_apply], refl}
  ... =  ((h₂.to_linear_map).comp ftt') x : by rw[Comm]
  ... = h₂ (ftt' x) :                       by {rw[comp_apply], refl}
  ... = (h₂ ∘ ftt') x :                     rfl),
},
have function.injective (ftt ∘ h₁),
from function.injective.comp injt $ equiv.injective $ linear_equiv.to_equiv h₁,
have function.injective (h₂  ∘ ftt'), from Comm' ▸ this,
show function.injective ftt',
from (equiv.comp_injective ftt' (linear_equiv.to_equiv h₂)).1 this
end

open tensor_product (smul_tmul) -- RF

/-- RF: A non-zero divisor in R remains a non-zero divisor on any flat R-module-/

theorem non_zero_divisor_of_flat (P : Type u) [add_comm_group P] [module R P]
  (hflP : flat R P) (r : R) (non_div : function.injective (λ (x : R), r * x)) :
  function.injective (λ (x : P), r • x) :=
let f : P →ₗ[R] P := linear_map_smul P r  in
let g : R →ₗ[R] R := linear_map_smul R r in
have h_inj : function.injective (ltensor P g), from flat_iff_ltensor_injective.1 hflP g non_div,
let h : P ⊗[R] R ≃ₗ P := tensor_product.rid R P in
have ltensor P g = rtensor R f , by
{
  apply tensor_product.ext,
  intros p r',
  repeat{rw [comp_apply]},
  exact calc
    (ltensor P g) (p ⊗ₜ[R] r')= (linear_map.id p) ⊗ₜ[R] (g r') : by refl
    ... = p ⊗ₜ[R] (r * r')                          : rfl
    ... = (r • p) ⊗ₜ[R] r'                          : (smul_tmul _ _ _).symm
    ... = (f p) ⊗ₜ[R] ( linear_map.id r')           : rfl
    ... = (rtensor R f) (p ⊗ₜ[R] r')        : by refl
},
have Comm : h ∘ (ltensor P g) = f ∘ h, by rw [this, tensor_product_rid_functorial P f],
have function.injective (h ∘ (ltensor P g)),
from function.injective.comp (equiv.injective (linear_equiv.to_equiv h)) h_inj,
have function.injective (f ∘ h), from Comm ▸ this,
show function.injective f, from (equiv.injective_comp (linear_equiv.to_equiv h) f).1 this


end module

namespace ring_hom

variables {A B C : Type*} [comm_ring A] [comm_ring B] [comm_ring C] {g : B →+* C} {f : A →+* B}

def flat (f : A →+* B) : Prop :=
by letI := f.to_algebra; exact module.flat A B

namespace flat

variable (A)

lemma id : (ring_hom.id A).flat := module.flat.self

variable {A}

lemma comp (hg : g.flat) (hf : f.flat) : (g.comp f).flat :=
begin
  letI := (g.comp f).to_algebra,
  letI := f.to_algebra,
  letI := g.to_algebra,
  letI : is_scalar_tower A B C :=
    is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  haveI : module.flat A B := hf,
  haveI : module.flat B C := hg,
  show module.flat A C,
  rw module.flat_iff_rtensor_injective,
  introsI N P _ _ _ _ φ hφ,
  have hφB := module.flat.base_change_injective B φ hφ,
  have hφBC := module.flat.base_change_injective C _ hφB,
  rw [module.flat.rtensor_injective_iff_ltensor_injective, ← linear_map.base_change_eq_ltensor],
end

end flat

end ring_hom
