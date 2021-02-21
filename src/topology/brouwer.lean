import analysis.normed_space.basic
import topology.instances.real
import dynamics.fixed_points.basic
import analysis.special_functions.pow
import topology.uniform_space.compact_separated

section brouwer
variables {ι : Type*} [fintype ι] [nonempty ι] (f : set.Icc (0 : ι → ℝ) 1 → set.Icc (0 : ι → ℝ) 1)
  (hf : continuous f)
  --(hf' : ∀ x : fin n → ℝ, (∀ i, x i ∈ set.Icc (0 : ℝ) 1) → ∀ i, f x i ∈ set.Icc (0 : ℝ) 1)

lemma lem {S : set nnreal} (hS : is_closed S) (hS' : ∀ ε > 0, ∃ x : nnreal, x ∈ S ∧ x < ε) : (0 : nnreal) ∈ S :=
begin
  refine is_closed_iff_nhds.mp hS 0 _,
  intros U hU,
  obtain ⟨ε, ⟨hε, hε'⟩⟩ := exists_Ico_subset_of_mem_nhds hU ⟨1, by norm_num⟩,
  obtain ⟨x, ⟨hx, hx'⟩⟩ := hS' _ hε,
  refine ⟨x, ⟨hε' _, hx⟩⟩,
  simp only [true_and, set.mem_Ico, zero_le'],
  exact hx'
end

include hf

lemma brouwer_aux_aux : ∀ (ε : ℝ) (hε : ε > 0), ∃ x : set.Icc (0 : ι → ℝ) 1, ∀ i : ι,
  (f x).1 i - x.1 i ≤ ε ∧ x.1 i - (f x).1 i ≤ ε :=
begin
  intros ε hε,
  haveI : compact_space (set.Icc (0 : ι → ℝ) 1) := by
  { exact ⟨compact_iff_compact_univ.1 compact_pi_Icc⟩, },
  have huf : uniform_continuous f,
  { exact compact_space.uniform_continuous_of_continuous hf },

end

lemma brouwer_aux : ∀ ε > 0, ∃ x, dist (f x) x < ε :=
begin
  intros ε₀ hε₀,
  set n := fintype.card ι with hn,
  have hn' : n > 0,
  { rw hn,
    exact fintype.card_pos_iff.mpr _inst_2, },
  obtain ⟨x, hx⟩ := brouwer_aux_aux f hf (ε₀ / 2) (half_pos hε₀),
  refine ⟨x, _⟩,
  have : dist (f x) x = dist (f x).1 x.1 := rfl, -- TODO
  rw [this, dist_pi_def, ←nnreal.coe_of_real _ (le_of_lt hε₀), nnreal.coe_lt_coe, finset.sup_lt_iff],
  { rintros i -,
    rw [nnreal.lt_of_real_iff_coe_lt, coe_nndist],
    obtain ⟨hx₁, hx₂⟩ := hx i,
    unfold dist, -- TODO
    rw abs_lt,
    split; linarith },
  { simpa only [bot_eq_zero, nnreal.of_real_pos] }
end

theorem brouwer : set.nonempty (function.fixed_points f) :=
begin
  have hcomp : compact_space (set.Icc (0 : ι → ℝ) 1) :=
    ⟨compact_iff_compact_univ.1 compact_pi_Icc⟩,
  set g : set.Icc (0 : ι → ℝ) 1 → nnreal := λ x, nndist (f x) x with hg,
  suffices : (0 : nnreal) ∈ g '' set.univ,
  { obtain ⟨x, ⟨-, hx⟩⟩ := this,
    exact ⟨x, nndist_eq_zero.1 hx⟩ },
  have hg : continuous g := continuous.nndist hf continuous_id,
  have closed_image : is_closed (g '' set.univ) :=
    is_compact.is_closed (is_compact.image (compact_iff_compact_univ.1 compact_pi_Icc) hg),
  apply lem closed_image,
  intros ε hε,
  obtain ⟨x, hx⟩ := brouwer_aux f hf ε hε,
  exact ⟨g x, ⟨by simp, hx⟩⟩,
end

end brouwer
