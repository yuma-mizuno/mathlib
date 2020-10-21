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

universe variables u

variables {R : Type u} {M N P Q : Type*} [comm_ring R]
variables [add_comm_group M] [module R M]
variables [add_comm_group N] [module R N]
variables [add_comm_group P] [module R P]
variables [add_comm_group Q] [module R Q]

section move_this

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
namespace tensor_product

variables {P' Q' : Type*}
variables [add_comm_group P'] [module R P']
variables [add_comm_group Q'] [module R Q']

lemma map_comp (f₂ : P →ₗ[R] P') (f₁ : M →ₗ[R] P) (g₂ : Q →ₗ[R] Q') (g₁ : N →ₗ[R] Q) :
  map (f₂.comp f₁) (g₂.comp g₁) = (map f₂ g₂).comp (map f₁ g₁) :=
by { ext1, simp only [linear_map.comp_apply, map_tmul] }

lemma lift_comp_map (i : P →ₗ[R] Q →ₗ[R] Q') (f : M →ₗ[R] P) (g : N →ₗ[R] Q) :
  (lift i).comp (map f g) = lift ((i.comp f).compl₂ g) :=
by { ext1, simp only [lift.tmul, map_tmul, linear_map.compl₂_apply, linear_map.comp_apply] }

end tensor_product

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

end linear_map

namespace module
open linear_map

variables (A B : Type*) [comm_ring A] [comm_ring B]
variables [algebra R A] [algebra R B] [algebra A B] [is_scalar_tower R A B]

instance : module A (A ⊗[R] M) :=
{ smul := λ a, rtensor M (algebra.lmul R A a),
  one_smul := λ x, by simp only [alg_hom.map_one, one_def, id.def, id_coe, rtensor_id],
  mul_smul := λ a b x, by simp only [alg_hom.map_mul, mul_def, rtensor_comp, comp_apply],
  smul_add := λ a x y, by simp only [map_add],
  smul_zero := λ a, by simp only [map_zero],
  add_smul := λ a b x, by simp only [alg_hom.map_add, add_apply, rtensor_add],
  zero_smul := λ x, by simp only [rtensor_zero, alg_hom.map_zero, zero_apply] }

def tensor_product.contract : B ⊗[A] (A ⊗[R] M) ≃ₗ[B] B ⊗[R] M :=
{ to_fun := _,
  map_smul' := _,
  .. (show semimodule.restrict_scalars R A (B ⊗[A] (A ⊗[R] M)) ≃ₗ[R] B ⊗[R] M,
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

-- lemma injective_rtensor_aux₁ (hM : flat R M) {n : ℕ} (L : submodule R (fin n →₀ R)) :
--   injective (L.subtype.rtensor M) :=
-- begin
--   -- rw injective_iff,
--   -- induction n with n IH,
--   { sorry },
-- end


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
