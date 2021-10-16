import analysis.calculus.times_cont_diff
import measure_theory.integral.interval_integral

/-!
-/

open filter function set metric topological_space interval_integral measure_theory
open measure_theory.measure_space (volume)
open_locale filter topological_space nnreal ennreal nat

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E]

section

localized "attribute [instance] borel" in borel_auto

lemma borel_space_borel (E : Type*) [topological_space E] : @borel_space E _ (borel E) := ⟨rfl⟩

localized "attribute [instance] borel_space_borel" in borel_auto

end

open_locale borel_auto

structure picard_lindelof (E : Type*) [normed_group E] [normed_space ℝ E] :=
(to_fun : ℝ → E → E)
(t_min t_max : ℝ)
(t₀ : Icc t_min t_max)
(x₀ : E)
(C R L : ℝ≥0)
(lipschitz' : ∀ t ∈ Icc t_min t_max, lipschitz_on_with L (to_fun t) (closed_ball x₀ R))
(cont : ∀ x ∈ closed_ball x₀ R, continuous_on (λ t, to_fun t x) (Icc t_min t_max))
(norm_le' : ∀ (t ∈ Icc t_min t_max) (x ∈ closed_ball x₀ R), ∥to_fun t x∥ ≤ C)
(mul_C_le_R : max (t_max - t₀) (t₀ - t_min) * C ≤ R)

namespace picard_lindelof

variables (v : picard_lindelof E)

instance : has_coe_to_fun (picard_lindelof E) := ⟨_, to_fun⟩

lemma t_min_le_t_max : v.t_min ≤ v.t_max := v.t₀.2.1.trans v.t₀.2.2

protected lemma nonempty_Icc : (Icc v.t_min v.t_max).nonempty := nonempty_Icc.2 v.t_min_le_t_max

protected lemma lipschitz_on_with {t} (ht : t ∈ Icc v.t_min v.t_max) :
  lipschitz_on_with v.L (v t) (closed_ball v.x₀ v.R) :=
v.lipschitz' t ht

protected lemma continuous_on :
  continuous_on (uncurry v) ((Icc v.t_min v.t_max).prod (closed_ball v.x₀ v.R)) :=
have continuous_on (uncurry (flip v)) ((closed_ball v.x₀ v.R).prod (Icc v.t_min v.t_max)),
  from continuous_on_prod_of_continuous_on_lipschitz_on _ v.L v.cont v.lipschitz',
this.comp continuous_swap.continuous_on preimage_swap_prod.symm.subset

lemma norm_le {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) {x : E} (hx : x ∈ closed_ball v.x₀ v.R) :
  ∥v t x∥ ≤ v.C :=
v.norm_le' _ ht _ hx

def t_dist : ℝ := max (v.t_max - v.t₀) (v.t₀ - v.t_min)

lemma t_dist_nonneg : 0 ≤ v.t_dist := le_max_iff.2 $ or.inl $ sub_nonneg.2 v.t₀.2.2

lemma dist_t₀_le (t : Icc v.t_min v.t_max) : dist t v.t₀ ≤ v.t_dist :=
begin
  rw [subtype.dist_eq, real.dist_eq],
  cases le_total t v.t₀ with ht ht,
  { rw [abs_of_nonpos (sub_nonpos.2 $ subtype.coe_le_coe.2 ht), neg_sub],
    exact (sub_le_sub_left t.2.1 _).trans (le_max_right _ _) },
  { rw [abs_of_nonneg (sub_nonneg.2 $ subtype.coe_le_coe.2 ht)],
    exact (sub_le_sub_right t.2.2 _).trans (le_max_left _ _) }
end

def proj : ℝ → Icc v.t_min v.t_max := proj_Icc v.t_min v.t_max v.t_min_le_t_max

lemma proj_coe (t : Icc v.t_min v.t_max) : v.proj t = t := proj_Icc_coe _ _

lemma proj_of_mem {t : ℝ} (ht : t ∈ Icc v.t_min v.t_max) : ↑(v.proj t) = t :=
by simp only [proj, proj_Icc_of_mem _ ht, subtype.coe_mk]

@[continuity] lemma continuous_proj : continuous v.proj := continuous_proj_Icc

structure fun_space :=
(to_fun : Icc v.t_min v.t_max → E)
(map_t₀' : to_fun v.t₀ = v.x₀)
(lipschitz' : lipschitz_with v.C to_fun)

namespace fun_space

variables {v} (f : fun_space v)

instance : has_coe_to_fun (fun_space v) := ⟨λ _, Icc v.t_min v.t_max → E, to_fun⟩

instance : inhabited v.fun_space :=
⟨⟨λ _, v.x₀, rfl, (lipschitz_with.const _).weaken (zero_le _)⟩⟩

protected lemma lipschitz : lipschitz_with v.C f := f.lipschitz'

protected lemma continuous : continuous f := f.lipschitz.continuous

def to_continuous_map : v.fun_space ↪ C(Icc v.t_min v.t_max, E) :=
⟨λ f, ⟨f, f.continuous⟩, λ f g h, by { cases f, cases g, simpa using h }⟩

instance : metric_space v.fun_space :=
metric_space.induced to_continuous_map to_continuous_map.injective infer_instance

lemma uniform_inducing_to_continuous_map : uniform_inducing (@to_continuous_map _ _ _ v) := ⟨rfl⟩

lemma range_to_continuous_map :
  range to_continuous_map =
    {f : C(Icc v.t_min v.t_max, E) | f v.t₀ = v.x₀ ∧ lipschitz_with v.C f} :=
begin
  ext f, split,
  { rintro ⟨⟨f, hf₀, hf_lip⟩, rfl⟩, exact ⟨hf₀, hf_lip⟩ },
  { rcases f with ⟨f, hf⟩, rintro ⟨hf₀, hf_lip⟩, exact ⟨⟨f, hf₀, hf_lip⟩, rfl⟩ }
end

variables [complete_space E]

instance : complete_space v.fun_space :=
begin
  refine (complete_space_iff_is_complete_range
    uniform_inducing_to_continuous_map).2 (is_closed.is_complete _),
  rw [range_to_continuous_map, set_of_and],
  refine (is_closed_eq (continuous_map.continuous_evalx _) continuous_const).inter _,
  have : is_closed {f : Icc v.t_min v.t_max → E | lipschitz_with v.C f} :=
    is_closed_set_of_lipschitz_with v.C,
  exact this.preimage continuous_map.continuous_coe
end

lemma map_t₀ : f v.t₀ = v.x₀ := f.map_t₀'

protected lemma mem_closed_ball (t : Icc v.t_min v.t_max) : f t ∈ closed_ball v.x₀ v.R :=
calc dist (f t) v.x₀ = dist (f t) (f.to_fun v.t₀) : by rw f.map_t₀'
                 ... ≤ v.C * dist t v.t₀          : f.lipschitz.dist_le_mul _ _
                 ... ≤ v.C * v.t_dist             : mul_le_mul_of_nonneg_left (v.dist_t₀_le _) v.C.2
                 ... ≤ v.R                        : by { rw mul_comm, exact v.mul_C_le_R }

def v_comp (t : ℝ) : E := v (v.proj t) (f (v.proj t))

lemma v_comp_apply_coe (t : Icc v.t_min v.t_max) : f.v_comp t = v t (f t) :=
by simp only [v_comp, proj_coe]

lemma continuous_v_comp : continuous f.v_comp :=
begin
  have := (continuous_subtype_coe.prod_mk f.continuous).comp v.continuous_proj,
  refine continuous_on.comp_continuous v.continuous_on this (λ x, _),
  exact ⟨(v.proj x).2, f.mem_closed_ball _⟩
end

lemma interval_integrable_v_comp (t₁ t₂ : ℝ) :
  interval_integrable f.v_comp volume t₁ t₂ :=
(f.continuous_v_comp).interval_integrable _ _

lemma norm_v_comp_le (t : ℝ) : ∥f.v_comp t∥ ≤ v.C :=
v.norm_le (v.proj t).2 $ f.mem_closed_ball _

lemma dist_apply_le_dist (f₁ f₂ : fun_space v) (t : Icc v.t_min v.t_max) :
  dist (f₁ t) (f₂ t) ≤ dist f₁ f₂ :=
@continuous_map.dist_apply_le_dist _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _

lemma dist_le_of_forall {f₁ f₂ : fun_space v} {d : ℝ} (h : ∀ t, dist (f₁ t) (f₂ t) ≤ d) :
  dist f₁ f₂ ≤ d :=
(@continuous_map.dist_le_iff_of_nonempty _ _ _ _ _ f₁.to_continuous_map f₂.to_continuous_map _
  v.nonempty_Icc.to_subtype).2 h

variables [second_countable_topology E]

def next (f : fun_space v) : fun_space v :=
{ to_fun := λ t, v.x₀ + ∫ τ : ℝ in v.t₀..t, f.v_comp τ,
  map_t₀' := by rw [integral_same, add_zero],
  lipschitz' := lipschitz_with.of_dist_le_mul $ λ t₁ t₂,
    begin
      rw [dist_add_left, dist_eq_norm,
        integral_interval_sub_left (f.interval_integrable_v_comp _ _)
          (f.interval_integrable_v_comp _ _)],
      exact norm_integral_le_of_norm_le_const (λ t ht, f.norm_v_comp_le _),
    end }

lemma next_apply (t : Icc v.t_min v.t_max) : f.next t = v.x₀ + ∫ τ : ℝ in v.t₀..t, f.v_comp τ := rfl

lemma has_deriv_within_at_next (t : Icc v.t_min v.t_max) :
  has_deriv_within_at (f.next ∘ v.proj) (v t (f t)) (Icc v.t_min v.t_max) t :=
begin
  haveI : fact ((t : ℝ) ∈ Icc v.t_min v.t_max) := ⟨t.2⟩,
  simp only [(∘), next_apply],
  refine has_deriv_within_at.const_add _ _,
  have : has_deriv_within_at (λ t : ℝ, ∫ τ in v.t₀..t, f.v_comp τ) (f.v_comp t)
    (Icc v.t_min v.t_max) t,
    from integral_has_deriv_within_at_right (f.interval_integrable_v_comp _ _)
      (f.continuous_v_comp.measurable_at_filter _ _) f.continuous_v_comp.continuous_within_at,
  rw v_comp_apply_coe at this,
  refine this.congr_of_eventually_eq_of_mem _ t.coe_prop,
  filter_upwards [self_mem_nhds_within],
  intros t' ht',
  rw v.proj_of_mem ht'
end

lemma dist_next_apply_le_of_le {f₁ f₂ : fun_space v} {n : ℕ} {d : ℝ} (hd : 0 ≤ d)
  (h : ∀ t, dist (f₁ t) (f₂ t) ≤ (v.L * |t - v.t₀|) ^ n / n! * d) (t : Icc v.t_min v.t_max) :
  dist (next f₁ t) (next f₂ t) ≤ (v.L * |t - v.t₀|) ^ (n + 1) / (n + 1)! * d :=
begin
  simp only [dist_eq_norm, next_apply, add_sub_add_left_eq_sub,
    ← interval_integral.integral_sub (interval_integrable_v_comp _ _ _)
      (interval_integrable_v_comp _ _ _), norm_integral_eq_norm_integral_Ioc,
    measure_theory.restrict_congr_set measure_theory.Ioc_ae_eq_Icc] at *,
  set I := interval (v.t₀ : ℝ) t,
  calc ∥∫ τ in I, f₁.v_comp τ - f₂.v_comp τ∥
      ≤ ∫ τ in I, v.L * ((v.L * |τ - v.t₀|) ^ n / n! * d) :
    begin
      refine norm_integral_le_of_norm_le (continuous.integrable_on_Icc _) _,
      { continuity },
      { refine (ae_restrict_mem measurable_set_interval).mono (λ τ hτ, _),
        refine (v.lipschitz_on_with (v.proj τ).2).norm_sub_le_of_le
          (f₁.mem_closed_ball _) (f₂.mem_closed_ball _) ((h _).trans_eq _),
        rw v.proj_of_mem,
        exact (interval_subset_Icc v.t₀.2 t.2 hτ) }
    end
  ... = (v.L * |t - v.t₀|) ^ (n + 1) / (n + 1)! * d : _,
  suffices : ∫ τ in I, |τ - v.t₀| ^ n = |t - v.t₀| ^ (n + 1) / (n + 1),
  { simp_rw [mul_pow, div_eq_mul_inv, mul_assoc, measure_theory.integral_mul_left,
      measure_theory.integral_mul_right, this, div_eq_mul_inv, pow_succ (v.L : ℝ),
      nat.factorial_succ, nat.cast_mul, nat.cast_succ, mul_inv₀, mul_assoc] },
  sorry
end

lemma dist_iterate_next_apply_le (f₁ f₂ : fun_space v) (n : ℕ) (t : Icc v.t_min v.t_max) :
  dist (next^[n] f₁ t) (next^[n] f₂ t) ≤ (v.L * |t - v.t₀|) ^ n / n! * dist f₁ f₂ :=
begin
  induction n with n ihn generalizing t,
  { rw [pow_zero, nat.factorial_zero, nat.cast_one, div_one, one_mul],
    exact dist_apply_le_dist f₁ f₂ t },
  { rw [iterate_succ_apply', iterate_succ_apply'],
    exact dist_next_apply_le_of_le dist_nonneg ihn _ }
end

lemma dist_iterate_next_le (f₁ f₂ : fun_space v) (n : ℕ) :
  dist (next^[n] f₁) (next^[n] f₂) ≤ (v.L * v.t_dist) ^ n / n! * dist f₁ f₂ :=
begin
  refine dist_le_of_forall (λ t, (dist_iterate_next_apply_le _ _ _ _).trans _),
  have : 0 ≤ dist f₁ f₂ := dist_nonneg,
  have : |(t - v.t₀ : ℝ)| ≤ v.t_dist := v.dist_t₀_le t,
  mono*; simp only [nat.cast_nonneg, mul_nonneg, nnreal.coe_nonneg, abs_nonneg, *]
end

end fun_space

variables [second_countable_topology E] [complete_space E]

lemma exists_contracting :
  ∃ (N : ℕ) K, contracting_with K ((fun_space.next : v.fun_space → v.fun_space)^[N]) :=
begin
  rcases ((real.tendsto_pow_div_factorial_at_top (v.L * v.t_dist)).eventually
    (gt_mem_nhds zero_lt_one)).exists with ⟨N, hN⟩,
  have : (0 : ℝ) ≤ (v.L * v.t_dist) ^ N / N!,
    from div_nonneg (pow_nonneg (mul_nonneg v.L.2 v.t_dist_nonneg) _) (nat.cast_nonneg _),
  exact ⟨N, ⟨_, this⟩, hN,
    lipschitz_with.of_dist_le_mul (λ f g, fun_space.dist_iterate_next_le f g N)⟩
end

lemma exists_fixed : ∃ f : v.fun_space, f.next = f :=
let ⟨N, K, hK⟩ := exists_contracting v in ⟨_, hK.is_fixed_pt_fixed_point_iterate⟩

lemma exists_solution :
  ∃ f : ℝ → E, f v.t₀ = v.x₀ ∧ ∀ t ∈ Icc v.t_min v.t_max,
    has_deriv_within_at f (v t (f t)) (Icc v.t_min v.t_max) t :=
begin
  rcases v.exists_fixed with ⟨f, hf⟩,
  refine ⟨f ∘ v.proj, _, λ t ht, _⟩,
  { simp only [(∘), proj_coe, f.map_t₀] },
  { simp only [(∘), v.proj_of_mem ht],
    lift t to Icc v.t_min v.t_max using ht,
    simpa only [hf, v.proj_coe] using f.has_deriv_within_at_next t }
end

end picard_lindelof
