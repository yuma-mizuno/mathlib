import measure_theory.measure.vector_measure
import measure_theory.integral.set_integral

noncomputable theory
open_locale classical measure_theory nnreal ennreal

variables {α β : Type*} {m : measurable_space α}

namespace measure_theory

namespace measure

include m

variables {μ ν : measure α} {f g : α → ℝ}

open topological_space simple_func finset

local infixr ` →ₛ `:25 := simple_func

variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [normed_space ℝ E] [complete_space E] [borel_space E]

-- private lemma integral_sum_measure_of_measurable
--   {f : α → E} (hf : measurable f) (μ : ℕ → measure α) (hμ : ∀ n, integrable f (μ n)) :
--   ∫ x, f x ∂(sum μ) = ∑' n, ∫ x, f x ∂(μ n) :=
-- begin
--   have hfsum : integrable f (sum μ) := sorry,
--   refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable hf hfsum) _,
--   have := simple_func.integrable_approx_on_univ hf hfsum _,
--   simpa only [simple_func.integral_add_measure _
--     (simple_func.integrable_approx_on_univ hf hfsum _)]
--     using (tendsto_integral_approx_on_univ_of_measurable hf hfsum)
-- end

-- lemma integral_sum_measure
--  {f : α → E} (μ : ℕ → measure α) (hμ : ∀ n, integrable f (μ n)) :
--   ∫ x, f x ∂(sum μ) = ∑' n, ∫ x, f x ∂(μ n) :=
-- begin
--   have h : ae_measurable f (sum μ) := sorry,
--   let g := h.mk f,
--   have A : f =ᵐ[sum μ] g := h.ae_eq_mk,
--   have B : ∀ n, f =ᵐ[μ n] g := λ n, A.filter_mono (ae_mono (measure.le_sum μ n)),
--   calc ∫ x, f x ∂(sum μ) = ∫ x, g x ∂(sum μ) : integral_congr_ae A
--   ... = ∫ x, g x ∂μ + ∫ x, g x ∂ν :
--     integral_add_measure_of_measurable h.measurable_mk ((integrable_congr B).1 hμ)
--       ((integrable_congr C).1 hν)
--   ... = ∫ x, f x ∂μ + ∫ x, f x ∂ν :
--     by { congr' 1, { exact integral_congr_ae B.symm }, { exact integral_congr_ae C.symm } }
-- end

lemma integral_sum_measure {μ : ℕ → measure α} (f : α →ₛ E) (hf : integrable f (sum μ)) :
  f.integral (sum μ) = ∑' n, f.integral (μ n) :=
begin
  simp only [integral_eq_sum_filter],-- ← sum_add_distrib, ← add_smul, measure.add_apply],
  rw tsum_sum,
  congr, ext1 x,
  rw sum_apply,
  rw ennreal.tsum_to_real_eq,
  all_goals { sorry },

  -- refine has_sum.map (distrib_mul_action.to_add_monoid_hom _ x) _,
  -- refine sum_congr rfl (λ x hx, _),
  -- rw [to_real_add];
  --   refine ne_of_lt ((integrable_iff_fin_meas_supp.1 _).meas_preimage_singleton_ne_zero
  --     (mem_filter.1 hx).2),
  -- exacts [hf.left_of_add_measure, hf.right_of_add_measure]
end

lemma integral_Union {f : α → E} {s : ℕ → set α}
  (hs₁ : ∀ n, measurable_set (s n)) (hs₂ : pairwise (disjoint on s))
  (hfm : measurable f) (hfi : integrable f μ) :
  ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
begin
  have hf : integrable f (sum (λ n, μ.restrict (s n))), sorry,
  rw restrict_Union hs₂ hs₁,
  refine tendsto_nhds_unique (tendsto_integral_approx_on_univ_of_measurable hfm hf) _,
  sorry
end

def with_density_vector_measure {m : measurable_space α} (μ : measure α) (f : α → E) :
  vector_measure α E :=
{ measure_of' := λ s, if measurable_set s then ∫ x in s, f x ∂μ else 0,
  empty' := by simp,
  not_measurable' := λ s hs, if_neg hs,
  m_Union' := λ s hs₁ hs₂,
  begin
    sorry
  end }

end measure

end measure_theory
