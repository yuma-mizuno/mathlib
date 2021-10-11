/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
import topology.homotopy.path
import category_theory.groupoid

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

universes u v

variables {X : Type u} {Y : Type v} [topological_space X] [topological_space Y]
variables {x₀ x₁ : X}

noncomputable theory

open_locale unit_interval

namespace path

namespace homotopy

private def refl_trans_symm_aux' (x : I × I) : ℝ :=
if (x.2 : ℝ) ≤ 1/2 then
  x.1 * 2 * x.2
else
  x.1 * (2 - 2 * x.2)

private lemma continuous_refl_trans_symm_aux' : continuous refl_trans_symm_aux' :=
begin
  refine continuous_if_le _ _ (continuous.continuous_on _) (continuous.continuous_on _) _,
  { continuity },
  { continuity },
  { continuity },
  { continuity },
  intros x hx,
  norm_num [hx, mul_assoc],
end

local attribute [continuity] continuous_refl_trans_symm_aux'

private lemma refl_trans_symm_aux'_mem_I (x : I × I) : refl_trans_symm_aux' x ∈ I :=
begin
  dsimp only [refl_trans_symm_aux'],
  split_ifs,
  { split,
    { apply mul_nonneg,
      { apply mul_nonneg,
        { unit_interval },
        { norm_num } },
      { unit_interval } },
    { rw [mul_assoc],
      apply mul_le_one,
      { unit_interval },
      { apply mul_nonneg,
        { norm_num },
        { unit_interval } },
      { linarith } } },
  { split,
    { apply mul_nonneg,
      { unit_interval },
      linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] },
    { apply mul_le_one,
      { unit_interval },
      { linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] },
      { linarith [unit_interval.nonneg x.2, unit_interval.le_one x.2] } } }
end

private def refl_trans_symm_aux (x : I × I) : I :=
⟨refl_trans_symm_aux' x, refl_trans_symm_aux'_mem_I x⟩

-- def refl_trans_symm (p : path x₀ x₁) : homotopy (path.refl x₀) (p.trans p.symm) :=
-- { to_fun := λ x, p (refl_trans_symm_aux x),
--   continuous_to_fun := by continuity!,
--   to_fun_zero := by norm_num [refl_trans_symm_aux, refl_trans_symm_aux'],
--   to_fun_one := by norm_num [refl_trans_symm_aux, refl_trans_symm_aux', path.trans],
--   prop' := _ }

def symm₂ {p q : path x₀ x₁} (h : p.homotopy q) : p.symm.homotopy q.symm :=
{ to_fun := λ x, h ⟨x.1, σ x.2⟩,
  continuous_to_fun := by continuity,
  to_fun_zero := by simp [path.symm],
  to_fun_one := by simp [path.symm],
  prop' := λ t x hx, begin
    cases hx,
    { rw hx, simp },
    { rw set.mem_singleton_iff at hx,
      rw hx,
      simp }
  end }

end homotopy

end path

def fundamental_groupoid (X : Type u) [topological_space X] := X

local attribute [reducible] fundamental_groupoid
local attribute [instance] path.homotopic.setoid

instance : category_theory.groupoid (fundamental_groupoid X) :=
{ hom := λ x y, path.homotopic.quotient x y,
  id := λ x, ⟦path.refl x⟧,
  comp := λ x y z p q, quotient.lift₂ (λ (l₁ : path x y) (l₂ : path y z), ⟦l₁.trans l₂⟧) begin
    rintros a₁ a₂ b₁ b₂ ⟨h₁⟩ ⟨h₂⟩,
    rw quotient.eq,
    exact ⟨h₁.hcomp h₂⟩,
  end p q,
  id_comp' := sorry,
  comp_id' := sorry,
  assoc' := sorry,
  inv := λ x y p, quotient.lift (λ l : path x y, ⟦l.symm⟧) begin
    rintros a b ⟨h⟩,
    rw quotient.eq,
    exact ⟨h.symm₂⟩,
  end p,
  inv_comp' := _,
  comp_inv' := _ }
