/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Rémy Degenne
-/
import measure_theory.measure_space
import algebra.big_operators.intervals
import data.finset.intervals

/-!
# Independence of sets of sets and measure spaces (σ-algebras)

* A family of sets of sets `π : ι → set (set α)` is independent with respect to measure `μ` if for
any finite set of indices `S = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, `μ (⋂ m in S, f i_m) = ∏ m in S, μ (f i_m) `. It will be used
for families of pi_systems.
* A family of measurable spaces (or σ-algebras) is independent if the family of sets of measurable
sets they define is independent. `m : ι → measurable_space α` is independent with
respect to measure `μ` if for any finite set of indices `S = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, `μ (⋂ m in S, f i_m) = ∏ m in S, μ (f i_m) `.
* Independence of sets (or events in probabilistic parlance) is defined as independence of the
measurable spaces they generate: a set `s` generates the measurable space with measurable sets
`∅, s, sᶜ, univ`.
* Independence of functions (or random variables) is also defined as independence of the measurable
spaces they generate : a function `f` for which we have a measurable space `m` on the codomain
generates `measurable_space.comap f m`.

## Main statements

* TODO: `indep_of_indep_sets_of_pi_system`: if π-systems are independent as sets of sets, then the
σ-algebras they generate are independent.
* `indep2_of_indep2_sets_of_pi_system`: variant with two π-systems.

## Implementation notes

We provide one main definition of independence:
* `indep_sets`: independence of a family of sets of sets `pi : ι → set (set α)`,
Three other independence notions are defined using `indep_sets`:
* `indep`: independence of a family of measurable spaces `m : ι → measurable_space α`,
* `indep_set`: independence of a family of sets `s : ι → set α`,
* `indep_fun`: independence of a family of functions. For measurable spaces
  `m : Π (x : ι), measurable_space (β x)`, we consider functions `f : Π (x : ι), α → β x`.

Additionally, we provide four corresponding statements for two measurable spaces (resp. sets of
sets, sets, functions) instead of a family.

The definition of independence for `indep_sets` uses finite sets (`finset`): it is a statement of
the form "for all finite sets...". An alternative and equivalent way of defining independence
would have been to use countable sets.
TODO: prove that equivalence.

## References

* Williams, David. Probability with martingales. Cambridge university press, 1991.
Part A, Chapter 4.
-/

open measure_theory
open_locale big_operators classical

section definitions

/-- A family of sets of sets `π : ι → set (set α)` is independent with respect to measure `μ` if for
any finite set of indices `S = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ π i_1, ..., f i_n ∈ π i_n`, `μ (⋂ m in S, f i_m) = ∏ m in S, μ (f i_m) `.
It will be used for families of pi_systems. -/
def indep_sets {α ι} [measurable_space α] (pi : ι → set (set α)) (μ : measure α) : Prop :=
∀ (S : finset ι) {f : ι → set α} (H : ∀ x, x ∈ S → f x ∈ pi x),
  μ (⋂ t ∈ S, f t) = ∏ t in S, μ (f t)

/-- Two sets of sets `p₁, p₂` are independent with respect to
measure `μ` if for any sets `t₁ ∈ p₁, t₂ ∈ p₂`, `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep2_sets {α} [measurable_space α] (p1 p2 : set (set α)) (μ : measure α) : Prop :=
∀ t1 t2 : set α, t1 ∈ p1 → t2 ∈ p2 → μ (t1 ∩ t2) = μ t1 * μ t2

/-- A family of measurable spaces (or σ-algebras) `m : ι → measurable_space α` is independent with
respect to measure `μ` if for any finite set of indices `S = {i_1, ..., i_n}`, for any sets
`f i_1 ∈ m i_1, ..., f i_n ∈ m i_n`, `μ (⋂ m in S, f i_m) = ∏ m in S, μ (f i_m) `. -/
def indep {α ι} (m : ι → measurable_space α) [measurable_space α] (μ : measure α) : Prop :=
indep_sets (λ x, (m x).is_measurable') μ

/-- Two measurable spaces (or σ-algebras) `m₁, m₂` are independent with respect to
measure `μ` if for any sets `t₁ ∈ m₁, t₂ ∈ m₂`, `μ (t₁ ∩ t₂) = μ (t₁) * μ (t₂)` -/
def indep2 {α} (m₁ : measurable_space α) (m₂ : measurable_space α) [measurable_space α]
  (μ : measure α) :
  Prop :=
indep2_sets (m₁.is_measurable') (m₂.is_measurable') μ

/-- A family of sets is independent if the family of measurable spaces they generate is
independent. For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def indep_set {α ι} [measurable_space α] (s : ι → set α) (μ : measure α) : Prop :=
indep (λ i, measurable_space.generate_from {s i}) μ

/-- Two sets are independent if the two measurable spaces they generate are independent.
For a set `s`, the generated measurable space has measurable sets `∅, s, sᶜ, univ`. -/
def indep2_set {α} [measurable_space α] {s t : set α} (μ : measure α) : Prop :=
indep2 (measurable_space.generate_from {s}) (measurable_space.generate_from {t}) μ

/-- A family of functions is independent if the family of measurable spaces they generate is
independent. For a function `f` with codomain having measurable space `m`, the generated measurable
space is `measurable_space.comap f m`. -/
def indep_fun {α ι} [measurable_space α] {β : ι → Type*} (m : Π (x : ι), measurable_space (β x))
  (f : Π (x : ι), α → β x) (μ : measure α) : Prop :=
indep (λ x, measurable_space.comap (f x) (m x)) μ

/-- Two functions are independent if the two measurable spaces they generate are independent.
For a function `f` with codomain having measurable space `m`, the generated measurable
space is `measurable_space.comap f m`. -/
def indep2_fun {α β γ} [measurable_space α] (mβ : measurable_space β) (mγ : measurable_space γ)
  {f : α → β} {g : α → γ} (μ : measure α) : Prop :=
indep2 (measurable_space.comap f mβ) (measurable_space.comap g mγ) μ

end definitions

section indep2

lemma indep2_sets.symm {α} {p₁ p₂ : set (set α)}[measurable_space α] {μ : measure α}
  (h : indep2_sets p₁ p₂ μ) :
  indep2_sets p₂ p₁ μ :=
by {intros t1 t2 ht1 ht2, rw [set.inter_comm, mul_comm], exact h t2 t1 ht2 ht1, }

lemma indep2.symm {α} {m₁ m₂ : measurable_space α} [measurable_space α] {μ : measure α}
  (h : indep2 m₁ m₂ μ) :
  indep2 m₂ m₁ μ :=
indep2_sets.symm h

lemma indep2_of_indep2_of_le_left {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep2 m₁ m₂ μ) (h31 : m₃ ≤ m₁) :
  indep2 m₃ m₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (h31 _ ht1) ht2

lemma indep2_of_indep2_of_le_right {α} {m₁ m₂ m₃: measurable_space α} [measurable_space α]
  {μ : measure α} (h_indep : indep2 m₁ m₂ μ) (h32 : m₃ ≤ m₂) :
  indep2 m₁ m₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (h32 _ ht2)

lemma indep2_sets_of_indep2_sets_of_le_left {α} {p₁ p₂ p₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep2_sets p₁ p₂ μ) (h31 : p₃ ⊆ p₁) :
  indep2_sets p₃ p₂ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (set.mem_of_subset_of_mem h31 ht1) ht2

lemma indep2_sets_of_indep2_sets_of_le_right {α} {p₁ p₂ p₃: set (set α)} [measurable_space α]
  {μ : measure α} (h_indep : indep2_sets p₁ p₂ μ) (h32 : p₃ ⊆ p₂) :
  indep2_sets p₁ p₃ μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 ht1 (set.mem_of_subset_of_mem h32 ht2)

lemma indep2_sets.union {α} [measurable_space α] {p₁ p₂ p' : set (set α)} {μ : measure α}
  (hyp₁ : indep2_sets p₁ p' μ) (hyp₂ : indep2_sets p₂ p' μ) :
  indep2_sets (p₁ ∪ p₂) p' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_union at ht1,
  cases ht1,
  { exact hyp₁ t1 t2 ht1 ht2, },
  { exact hyp₂ t1 t2 ht1 ht2, },
end

lemma indep2_sets.union_iff {α} [measurable_space α] {p₁ p₂ p' : set (set α)} {μ : measure α} :
  indep2_sets (p₁ ∪ p₂) p' μ ↔ indep2_sets p₁ p' μ ∧ indep2_sets p₂ p' μ :=
⟨λ h, ⟨indep2_sets_of_indep2_sets_of_le_left h (set.subset_union_left p₁ p₂),
    indep2_sets_of_indep2_sets_of_le_left h (set.subset_union_right p₁ p₂)⟩,
  λ h, indep2_sets.union h.left h.right⟩

lemma indep2_sets.Union {α ι} [measurable_space α] {p : ι → set (set α)} {p' : set (set α)}
  {μ : measure α} (hyp : ∀ n, indep2_sets (p n) p' μ) :
  indep2_sets (⋃ n, p n) p' μ :=
begin
  intros t1 t2 ht1 ht2,
  rw set.mem_Union at ht1,
  cases ht1 with n ht1,
  exact hyp n t1 t2 ht1 ht2,
end

lemma indep2_sets.inter {α} [measurable_space α] {p₁ p' : set (set α)} (p₂ : set (set α))
  {μ : measure α} (hyp₁ : indep2_sets p₁ p' μ) :
  indep2_sets (p₁ ∩ p₂) p' μ :=
λ t1 t2 ht1 ht2, hyp₁ t1 t2 ((set.mem_inter_iff _ _ _).mp ht1).left ht2

lemma indep2_sets.Inter {α ι} [measurable_space α] {p : ι → set (set α)} {p' : set (set α)}
  {μ : measure α} (hyp : ∃ n, indep2_sets (p n) p' μ) :
  indep2_sets (⋂ n, p n) p' μ :=
by {intros t1 t2 ht1 ht2, cases hyp with n hyp, exact hyp t1 t2 (set.mem_Inter.mp ht1 n) ht2 }

end indep2

section from_indep_to_indep2

lemma indep2_sets_of_indep_sets {α ι} {m : ι → set (set α)} [measurable_space α] {μ : measure α}
  (h_indep : indep_sets m μ) {i j : ι} (hij : i ≠ j) :
  indep2_sets (m i) (m j) μ :=
begin
  intros t₁ t₂ ht₁ ht₂,
  have hf_m : ∀ (x : ι), x ∈ {i, j} → (ite (x=i) t₁ t₂) ∈ m x,
  { intros x hx,
    rw finset.mem_insert at hx,
    cases hx,
    { simp [hx, ht₁], },
    { simp [finset.mem_singleton.mp hx, hij.symm, ht₂], }, },
  have h1 : t₁ = ite (i = i) t₁ t₂, by simp only [if_true, eq_self_iff_true],
  have h2 : t₂ = ite (j = i) t₁ t₂, by simp only [hij.symm, if_false],
  have h_inter : (⋂ (t : ι) (H : t ∈ ({i, j} : finset ι)), ite (t = i) t₁ t₂)
    = (ite (i = i) t₁ t₂) ∩ (ite (j = i) t₁ t₂),
  by simp only [finset.bInter_singleton, finset.bInter_insert],
  have h_prod : (∏ (t : ι) in ({i, j} : finset ι), μ (ite (t = i) t₁ t₂))
    = μ (ite (i = i) t₁ t₂) * μ (ite (j = i) t₁ t₂),
  by simp only [hij, finset.prod_singleton, finset.prod_insert, not_false_iff,
    finset.mem_singleton],
  rw h1,
  nth_rewrite 1 h2,
  nth_rewrite 3 h2,
  rw [←h_inter, ←h_prod, h_indep {i, j} hf_m],
end

lemma indep2_of_indep {α ι} {m : ι → measurable_space α} [measurable_space α] {μ : measure α}
  (h_indep : indep m μ) {i j : ι} (hij : i ≠ j) :
  indep2 (m i) (m j) μ :=
begin
  change indep2_sets ((λ x, (m x).is_measurable') i) ((λ x, (m x).is_measurable') j) μ,
  exact indep2_sets_of_indep_sets h_indep hij,
end

end from_indep_to_indep2

/-!
### π-system lemma

Independence of measurable spaces is equivalent to independence of generating π-systems.
-/

section from_measurable_spaces_to_sets_of_sets

lemma indep_sets_of_indep {α ι} [measurable_space α] {μ : measure α} {m : ι → measurable_space α}
  {p : ι → set (set α)} (hps : ∀ n, m n = measurable_space.generate_from (p n))
  (h_indep : indep m μ) :
  indep_sets p μ :=
begin
  refine (λ S f hfp, h_indep S (λ x hxS, _)),
  dsimp only,
  rw hps x,
  exact measurable_space.is_measurable_generate_from (hfp x hxS),
end

lemma indep2_sets_of_indep2 {α} [measurable_space α] {μ : measure α} {p1 p2 : set (set α)}
  (h_indep : indep2 (measurable_space.generate_from p1) (measurable_space.generate_from p2) μ) :
  indep2_sets p1 p2 μ :=
λ t1 t2 ht1 ht2, h_indep t1 t2 (measurable_space.is_measurable_generate_from ht1)
  (measurable_space.is_measurable_generate_from ht2)

end from_measurable_spaces_to_sets_of_sets

section from_pi_systems_to_measurable_spaces

private lemma indep2_of_indep2_sets_of_pi_system_aux {α} {m2 : measurable_space α}
  {m : measurable_space α} {μ : measure α} [probability_measure μ]
  {p1 p2 : set (set α)} (h2 : m2 ≤ m)
  (hp2 : is_pi_system p2) (hpm2 : m2 = measurable_space.generate_from p2)
  (hyp : indep2_sets p1 p2 μ) (t1 t2 : set α) (ht1 : t1 ∈ p1) (ht2m : m2.is_measurable' t2) :
  μ (t1 ∩ t2) = μ t1 * μ t2 :=
begin
  let μ_inter := μ.restrict t1,
  let ν := (μ t1) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  have h_μ_finite := @restrict.finite_measure α _ t1 μ (measure_lt_top μ t1),
  have h_ν_finite := μ.smul_finite (measure_lt_top μ t1),
  have h_agree : ∀ (t : set α), t ∈ p2 → μ_inter t = ν t,
  { intros t ht,
    have ht2 : m.is_measurable' t,
    { refine h2 _ _,
      rw hpm2,
      exact measurable_space.is_measurable_generate_from ht, },
    rw [measure.restrict_apply ht2, measure.smul_apply, set.inter_comm],
    exact hyp t1 t ht1 ht, },
  have hμν : ∀ (t : set α), m2.is_measurable' t → μ_inter t = ν t,
  from @ext_on_sigma_algebra_of_generate_finite α m μ_inter ν h_μ_finite h_ν_finite p2 h_agree
      m2 h2 hpm2 hp2 h_univ,
  rw [set.inter_comm, ←@measure.restrict_apply α _ μ t1 t2 (h2 t2 ht2m)],
  exact hμν t2 ht2m,
end

lemma indep2_of_indep2_sets_of_pi_system {α} {m1 m2 : measurable_space α} {m : measurable_space α}
  {μ : measure α} [probability_measure μ] {p1 p2 : set (set α)}
  (h1 : m1 ≤ m) (h2 : m2 ≤ m)
  (hp1 : is_pi_system p1) (hp2 : is_pi_system p2) (hpm1 : m1 = measurable_space.generate_from p1)
  (hpm2 : m2 = measurable_space.generate_from p2) (hyp : indep2_sets p1 p2 μ) :
  indep2 m1 m2 μ :=
begin
  intros t1 t2 ht1 ht2,
  let μ_inter := μ.restrict t2,
  let ν := (μ t2) • μ,
  have h_univ : μ_inter set.univ = ν set.univ,
  by rw [measure.restrict_apply_univ, measure.smul_apply, measure_univ, mul_one],
  have h_μ_finite := @restrict.finite_measure α _ t2 μ (measure_lt_top μ t2),
  have h_ν_finite := μ.smul_finite (measure_lt_top μ t2),
  have h_side1 := indep2_of_indep2_sets_of_pi_system_aux h2 hp2 hpm2 hyp,
  have h_agree : ∀ (t : set α), t ∈ p1 → μ_inter t = ν t,
  { intros t ht,
    have ht1 : m.is_measurable' t,
    { refine h1 _ _,
      rw hpm1,
      exact measurable_space.is_measurable_generate_from ht, },
    rw [measure.restrict_apply ht1, measure.smul_apply, mul_comm],
    exact h_side1 t t2 ht ht2, },
  have hμν : ∀ (t : set α), m1.is_measurable' t → μ_inter t = ν t,
  from @ext_on_sigma_algebra_of_generate_finite α m μ_inter ν h_μ_finite h_ν_finite p1 h_agree
    m1 h1 hpm1 hp1 h_univ,
  rw [mul_comm, ←@measure.restrict_apply α _ μ t2 t1 (h1 t1 ht1)],
  exact hμν t1 ht1,
end

end from_pi_systems_to_measurable_spaces

















section pi_systems

/-- From a set of finsets `S` and a family of sets of sets `π`, define the set of sets `s` that can
be written as `s = ⋂ x ∈ t, f x` for some `t` in `S` and sets `f x ∈ π x`.
If `S` is union-closed and `π` is a family of π-systems, then it is a pi-system.
The name expresses that it is the union over `t ∈ S` of sets that are written as intersections.
The π-systems used to prove Komogorov's 0-1 law are of that form. -/
def pi_system_Union_Inter {α ι} (π : ι → set (set α)) (S : set (finset ι)) : set (set α) :=
{s : set α | ∃ (t : finset ι) (htS : t ∈ S) (f : ι → set α) (hf : ∀ x, x ∈ t → f x ∈ π x),
  s = ⋂ x (hxt : x ∈ t), f x}

/-- A set `s` is sup-closed if for all `t₁, t₂ ∈ s`, `t₁ ⊔ t₂ ∈ s`. -/
def sup_closed {α} [has_sup α] (s : set α) : Prop := ∀ t1 t2, t1 ∈ s → t2 ∈ s → t1 ⊔ t2 ∈ s

lemma sup_closed_singleton {α} [semilattice_sup α] (q : α) : sup_closed ({q} : set α) :=
begin
  intros p1 p2 p1_mem p2_mem,
  rw set.mem_singleton_iff at p1_mem p2_mem ⊢,
  rw [p1_mem, p2_mem, sup_idem],
end

lemma sup_closed_tail_finset_set (N : ℕ) :
  sup_closed {s : finset ℕ | ∃ r : ℕ, s = finset.Ico N (N+r+1)} :=
begin
  rintros s1 s2 ⟨r1, hs1⟩ ⟨r2, hs2⟩,
  use (r1 ⊔ r2),
  have hr : ∀ r : ℕ, N ≤ N + r + 1,
  { intro r,
    rw add_assoc,
    nth_rewrite 0 ←add_zero N,
    exact add_le_add_left (zero_le _) N, },
  rw [finset.sup_eq_union s1 s2, hs1, hs2, sup_eq_max, ←max_add_add_left, ←max_add_add_right],
  have h := finset.Ico.union' (hr r1) (hr r2),
  rw min_self at h,
  exact h,
end

lemma finset.Inter_inter_Inter_eq_Inter_ite {α ι} (p1 p2 : finset ι) (f1 f2 : ι → set α) :
  (⋂ (i : ι) (hp : i ∈ p1), f1 i) ∩ (⋂ (i : ι) (hp : i ∈ p2), f2 i)
  = ⋂ (i : ι) (hp : i ∈ p1 ∪ p2),
    (ite (i ∈ p1) (f1 i) set.univ) ∩ (ite (i ∈ p2) (f2 i) set.univ) :=
begin
  ext,
  simp_rw [set.mem_inter_iff, set.mem_Inter, set.mem_inter_iff],
  split; intro hx,
  { intros i hpi,
    split_ifs with hi1; simp [hi1, h, hx], },
  { split; intros i hpi; specialize hx i,
    { have hpi_ : i ∈ p1 ∪ p2, from finset.mem_union.mpr (or.inl hpi),
      cases (hx hpi_) with hx _,
      simpa only [if_true, hpi] using hx, },
    { have hpi_ : i ∈ p1 ∪ p2, from finset.mem_union.mpr (or.inr hpi),
      cases (hx hpi_) with _ hx,
      simpa only [if_true, hpi] using hx, }, },
end

lemma is_pi_system_pi_system_Union_Inter {α ι} (pi : ι → set (set α))
  (hpi : ∀ x, is_pi_system (pi x)) (S : set (finset ι)) (h_sup : sup_closed S) :
  is_pi_system (pi_system_Union_Inter pi S) :=
begin
  intros t1 t2 ht1 ht2 h_nonempty,
  simp_rw [pi_system_Union_Inter, set.mem_set_of_eq],
  rcases ht1 with ⟨p1, hp1S, f1, hf1m, ht1_eq⟩,
  rcases ht2 with ⟨p2, hp2S, f2, hf2m, ht2_eq⟩,
  let g := λ n, (ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ),
  use [p1 ∪ p2, h_sup p1 p2 hp1S hp2S, g],
  have h_inter_eq : t1 ∩ t2 = ⋂ (i : ι) (hp : i ∈ p1 ∪ p2), g i,
  { rw [ht1_eq, ht2_eq],
    exact finset.Inter_inter_Inter_eq_Inter_ite p1 p2 f1 f2, },
  split,
  { intros n hn,
    change ((ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ)) ∈ pi n,
    split_ifs with hn1 hn2,
    { refine hpi n (f1 n) (f2 n) (hf1m n hn1) (hf2m n hn2) _,
      rw h_inter_eq at h_nonempty,
      by_contra,
      rw set.not_nonempty_iff_eq_empty at h,
      have h_empty :(⋂ (i : ι) (hp : i ∈ p1 ∪ p2), g i) = ∅,
      { refine le_antisymm (set.Inter_subset_of_subset n _) (set.empty_subset _),
        refine set.Inter_subset_of_subset hn _,
        have h_gn_eq : g n = f1 n ∩ f2 n,
        { change (ite (n ∈ p1) (f1 n) set.univ) ∩ (ite (n ∈ p2) (f2 n) set.univ) = f1 n ∩ f2 n,
          simp only [if_true, hn1, hn2], },
        rw [h_gn_eq, h], },
      exact (set.not_nonempty_iff_eq_empty.mpr h_empty) h_nonempty, },
    { simp [hf1m n hn1], },
    { simp [hf2m n h], },
    { exfalso,
      rw [finset.mem_union, ←@not_not (n ∈ p1 ∨ n ∈ p2)] at hn,
      exact hn (by simp [hn1, h]), }, },
  { exact h_inter_eq, },
end

lemma generate_from_pi_system_Union_Inter_le {α ι} {m : measurable_space α}
  {s : ι → measurable_space α} (h : ∀ n, s n ≤ m) (pi : ι → set (set α)) (S : set (finset ι))
  (hpis : ∀ n, s n = measurable_space.generate_from (pi n)) :
  measurable_space.generate_from (pi_system_Union_Inter pi S) ≤ m :=
begin
  refine measurable_space.generate_from_le (λ t ht, _),
  rcases ht with ⟨ht_p, ht_p_mem, ft, hft_mem_pi, ht_eq⟩,
  rw ht_eq,
  refine finset.is_measurable_bInter _ (λ x, _),
  by_cases hx : x ∈ ht_p; intro hx_mem,
  { refine (h x) _ _,
    rw hpis x,
    exact measurable_space.is_measurable_generate_from (hft_mem_pi x hx), },
  { exfalso,
    exact hx hx_mem, },
end

lemma subset_pi_system_Union_Inter {α ι} (pi : ι → set (set α)) (S : set (finset ι))
  (h_univ : ∀ x, set.univ ∈ (pi x)) {x : ι} {s :finset ι} (hsS : s ∈ S) (hxs : x ∈ s) :
  pi x ⊆ pi_system_Union_Inter pi S :=
begin
  intros t ht_pin,
  rw [pi_system_Union_Inter, set.mem_set_of_eq],
  use [s, hsS, (λ i, ite (i = x) t set.univ)],
  split,
  { intros m h_pm,
    split_ifs,
    { rwa h, },
    { exact h_univ m,}, },
  { ext,
    simp_rw set.mem_Inter,
    split; intro hx1,
    { intros i h_p_i,
      split_ifs,
      { exact hx1, },
      { exact set.mem_univ _, }, },
    { specialize hx1 x hxs,
      simpa using hx1, }, },
end

lemma le_generate_from_pi_system_Union_Inter {α ι} {s : ι → measurable_space α}
  {pi : ι → set (set α)} (S : set (finset ι))
  (hpis : ∀ n, s n = measurable_space.generate_from (pi n)) (h_univ : ∀ n, set.univ ∈ (pi n))
  {x : ι} {t : finset ι} (htS : t ∈ S) (hxt : x ∈ t) :
  s x ≤ measurable_space.generate_from (pi_system_Union_Inter pi S) :=
begin
  rw hpis x,
  refine measurable_space.generate_from_le_generate_from _,
  exact subset_pi_system_Union_Inter pi S h_univ htS hxt,
end

lemma measurable_subset_pi_system_Union_Inter {α ι} (s : ι → measurable_space α)
  {S : set (finset ι)} {i : ι} {p : finset ι} (hpS : p ∈ S) (hpi : i ∈ p) :
  set_of (s i).is_measurable' ⊆ pi_system_Union_Inter (λ n, (s n).is_measurable') S :=
begin
  intros t ht,
  rw pi_system_Union_Inter,
  rw set.mem_set_of_eq at ht ⊢,
  let g := λ n, ite (n=i) t set.univ,
  use [p, hpS, g],
  split,
  { intros j hj,
    change (s j).is_measurable' (ite (j=i) t set.univ),
    split_ifs with hji,
    { rwa hji, },
    { exact @is_measurable.univ α (s j), }, },
  { ext,
    simp_rw set.mem_Inter,
    split; intro hx,
    { intros j hj,
      change x ∈ ite (j=i) t set.univ,
      split_ifs; simp [hx], },
    { specialize hx i hpi,
      change x ∈ ite (i=i) t set.univ at hx,
      simpa using hx, }, },
end

lemma pi_system_Union_Inter_subset_measurable {α ι} (s : ι → measurable_space α)
  (S : set (finset ι)) :
  pi_system_Union_Inter (λ n, (s n).is_measurable') S
    ⊆ (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), s i).is_measurable' :=
begin
  intros t ht,
  rw [pi_system_Union_Inter, set.mem_set_of_eq] at ht,
  rcases ht with ⟨pt, hpt, ft, ht_m, ht_eq⟩,
  have h_i : ∀ i, i ∈ pt
    → (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), s i).is_measurable' (ft i),
  { intros i hi,
    have h_le : s i ≤ (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), s i),
    { have hi' : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p,
      { use pt,
        exact ⟨hpt, hi⟩, },
      exact le_bsupr i hi', },
    exact h_le (ft i) (ht_m i hi), },
  subst ht_eq,
  apply finset.is_measurable_bInter,
  intros i hipt,
  exact h_i i hipt,
end

lemma Sup_prop_eq_generate_from_pi_system_Union_Inter {α ι} (s : ι → measurable_space α)
  (S : set (finset ι)) :
  (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), s i) = measurable_space.generate_from
    (pi_system_Union_Inter (λ n, (s n).is_measurable') S) :=
begin
  refine le_antisymm _ _,
  { refine bsupr_le (λ i hi, _),
    rcases hi with ⟨p, hpS, hpi⟩,
    rw ← @measurable_space.generate_from_is_measurable α (s i),
    refine measurable_space.generate_from_le_generate_from _,
    exact measurable_subset_pi_system_Union_Inter s hpS hpi, },
  rw ← @measurable_space.generate_from_is_measurable α
    (⨆ (i : ι) (hi : ∃ (p : finset ι) (hp : p ∈ S), i ∈ p), s i),
  exact measurable_space.generate_from_le_generate_from
    (pi_system_Union_Inter_subset_measurable s S),
end

end pi_systems

section indep_of_indep_sets_of_pi_system

lemma pi_system_indep_insert {α ι} [measurable_space α] {μ : measure α} {pi : ι → set (set α)}
  (hp_ind : indep_sets pi μ) {a : ι} {S : finset ι} (haS : a ∉ S) :
  indep2_sets (pi_system_Union_Inter pi {S}) (pi a) μ :=
begin
  intros t1 t2 ht1_mem_pi ht2_mem_piNsucc,
  rcases ht1_mem_pi with ⟨prop1, ht1_prop1_mem, ft1, ht1_ft1_mem, ht1_eq⟩,
  rw set.mem_singleton_iff at ht1_prop1_mem,
  simp_rw ht1_prop1_mem at ht1_ft1_mem,
  let f1 := λ n, ite (n=a) t2 (ite (n ∈ S) (ft1 n) set.univ),
  have h_f1_mem : ∀ n, n ∈ insert a S → f1 n ∈ pi n,
  { intros n prop_n,
    change ite (n = a) t2 (ite (n ∈ S) (ft1 n) set.univ) ∈ pi n,
    split_ifs with hn,
    { rwa hn, },
    { exact ht1_ft1_mem n h, },
    { exfalso,
      rw [finset.mem_insert, ←@not_not (n = a ∨ n ∈ S)] at prop_n,
      exact prop_n (by simp [hn, h]), }, },
  have h_f1_mem_S : ∀ n, n ∈ S → f1 n ∈ pi n,
  { intros x hxS,
    exact h_f1_mem x (by simp [hxS]), },
  have h_t1 : t1 = ⋂ (n : ι) (h : n ∈ S), f1 n,
  { suffices h_forall : ∀ n (h : n ∈ S), f1 n = ft1 n,
    { rw ht1_eq,
      ext,
      simp_rw [set.mem_Inter, ht1_prop1_mem],
      split; intros hx i hiN; specialize hx i hiN,
      { rwa h_forall i hiN, },
      { rwa ←h_forall i hiN, }, },
    intros n prop_n,
    have h_n_ne_succ : ¬ n = a,
    { by_contra hna,
      rw hna at prop_n,
      exact haS prop_n, },
    change ite (n=a) t2 (ite (n ∈ S) (ft1 n) set.univ) = ft1 n,
    simp [prop_n, h_n_ne_succ], },
  have h_t2 : t2 = f1 a,
  { change t2 = ite (a=a) t2 (ite (a ∈ S) (ft1 a) set.univ),
    simp, },
  have h_t1_inter_t2 : t1 ∩ t2 = ⋂ (n : ι) (h : n ∈ insert a S), f1 n,
  by rw [h_t1, h_t2, finset.bInter_insert, set.inter_comm],
  have h_μ_inter : μ (t1 ∩ t2) = ∏ n in insert a S,μ (f1 n),
  by rw [h_t1_inter_t2, ←hp_ind (insert a S) h_f1_mem],
  have h_μ_t1 : μ t1 = ∏ n in S, μ (f1 n), by rw [h_t1, ←hp_ind S h_f1_mem_S],
  rw [h_μ_inter, finset.prod_insert haS, h_t2, mul_comm, h_μ_t1],
end

lemma indep_of_pi_system_indep {α ι} (m : measurable_space α) (s : ι → measurable_space α)
  (μ : @measure_theory.measure α m) [probability_measure μ] (h : ∀ n, s n ≤ m)
  (pi : ι → set (set α)) (h_pi : ∀ n, is_pi_system (pi n)) (hp_univ : ∀ n, set.univ ∈ pi n)
  (hps : ∀ n, s n = measurable_space.generate_from (pi n)) (hp_ind : indep_sets pi μ) :
  indep s μ :=
begin
  refine finset.induction (by simp [measure_univ]) _,
  intros a S ha_notin_S h_rec f hf_m,
  have hf_m_S : ∀ x, x ∈ S → (s x).is_measurable' (f x), from λ x hx, hf_m x (by simp [hx]),
  rw [finset.bInter_insert, finset.prod_insert ha_notin_S, ←h_rec hf_m_S],
  -- define π systems and generated σ-algebras
  let p_ := pi_system_Union_Inter pi {S},
  let S_ := measurable_space.generate_from p_,
  have hpS : S_ = measurable_space.generate_from p_, from rfl,
  have h_generated : ∀ n : ι, n ∈ S → s n ≤ S_,
  from (λ n hn, le_generate_from_pi_system_Union_Inter {S} hps hp_univ (set.mem_singleton _) hn),
  have h_indep : indep2 S_ (s a) μ,
  { have hp_ : is_pi_system p_,
    from is_pi_system_pi_system_Union_Inter pi h_pi {S} (sup_closed_singleton S),
    have hS : S_ ≤ m, from generate_from_pi_system_Union_Inter_le h pi {S} hps,
    have h_two : indep2_sets p_ (pi a) μ → indep2 S_ (s a) μ,
    from indep2_of_indep2_sets_of_pi_system hS (h a) hp_ (h_pi a) hpS (hps a),
    exact h_two (pi_system_indep_insert hp_ind ha_notin_S), },
  have ht1m : S_.is_measurable' (⋂ (n : ι) (H :n ∈ S), f n),
  { have h_S_f : ∀ i (hi : i ∈ S), S_.is_measurable' (f i),
    from (λ i hi, (h_generated i hi) (f i) (hf_m_S i hi)),
    exact @finset.is_measurable_bInter α ι S_ f _ (λ i hi, h_S_f i hi), },
  have ht2m : (s a).is_measurable' (f a), from hf_m a (by simp),
  rw [set.inter_comm, mul_comm],
  exact h_indep (⋂ (n : ι) (H : n ∈ S), f n) (f a) ht1m ht2m,
end

end indep_of_indep_sets_of_pi_system

/-! ### Kolmogorov's 0-1 law -/

section lattice

lemma bsupr_le_of_mp {α} {ι} [complete_lattice α] {p q : ι → Prop} {f : ι → α}
  (h : ∀ i,  p i → q i) :
  (⨆ i (hi : p i), f i) ≤ (⨆ i (hi : q i), f i) :=
begin
  suffices h_forall : ∀ i, (⨆ (hi : p i), f i) ≤ ⨆ (hi : q i), f i,
  { rw supr_le_iff,
    exact (λ i, le_trans (h_forall i) (le_supr _ i)), },
  simp_rw supr_le_iff,
  exact (λ i pi, le_supr (λ (hqi : q i), f i) (h i pi)),
end

lemma binfi_le_of_mp {α} {ι} [complete_lattice α] {p q : ι → Prop} {f : ι → α}
  (h : ∀ i,  p i → q i) :
  (⨅ i (hi : q i), f i) ≤ (⨅ i (hi : p i), f i) :=
@bsupr_le_of_mp (order_dual α) ι _ p q f h

lemma le_head_n {α} [complete_lattice α] (s : ℕ → α) {i n : ℕ} (hin : i < n) : s i ≤ ⨆ j < n, s j :=
le_bsupr i hin

lemma head_n_le {α} [complete_lattice α] {m : α} (s : ℕ → α) (n : ℕ) (h_le : ∀ n, s n ≤ m) :
  (⨆ i < n, s i) ≤ m :=
bsupr_le (λ i hi, h_le i)

lemma head_n_mono {α} [complete_lattice α] (s : ℕ → α) {n m : ℕ} (h : n ≤ m) :
  (⨆ i < n, s i) ≤ ⨆ i < m, s i :=
bsupr_le_of_mp (λ i hi, lt_of_lt_of_le hi h)

lemma supr_eq_supr_head_n {α} [complete_lattice α] (s : ℕ → α) : supr s = ⨆ n, ⨆ i < n, s i :=
le_antisymm (supr_le (λ i, le_trans (le_head_n s (nat.lt_succ_self i))
    (le_supr (λ i, (⨆ (j : ℕ) (H : j < i), s j)) (i+1))))
  (supr_le (λ i, bsupr_le_supr (λ n, n < i) (λ n, s n)))

lemma le_tail_n {α} [complete_lattice α] (s : ℕ → α) {i n : ℕ} (hin : n ≤ i) : s i ≤ ⨆ i ≥ n, s i :=
le_bsupr i hin

lemma tail_n_le {α} [complete_lattice α] {m : α} (s : ℕ → α) (n : ℕ) (h_le : ∀ n, s n ≤ m) :
  (⨆ i ≥ n, s i) ≤ m :=
bsupr_le (λ i hi, (h_le i))

lemma tail_n_le_supr {α} [complete_lattice α] (s : ℕ → α) (n : ℕ) : (⨆ i ≥ n, s i) ≤ supr s :=
bsupr_le_supr (λ i, i ≥ n) (λ i, (s i))

/-- TODO: rename, or find existing equivalent definition -/
def tail {α} [has_Sup α] [has_Inf α] (s : ℕ → α) : α := ⨅ n, ⨆ i ≥ n, s i

lemma tail_le_tail_n {α} [complete_lattice α] (s : ℕ → α) (n : ℕ) : tail s ≤ ⨆ i ≥ n, s i :=
infi_le (λ n, ⨆ i ≥ n, s i) n

lemma tail_le {α} [complete_lattice α] {m : α} {s : ℕ → α} (h_le : ∀ n, s n ≤ m) : tail s ≤ m :=
le_trans (tail_le_tail_n s 0) (tail_n_le s 0 h_le)

end lattice

section zero_one_law

lemma measure_eq_zero_or_one_or_top_of_indep_self {α} [measurable_space α] {μ : measure α}
  {m : measurable_space α} (h_indep : @indep2 α m m _inst_1 μ) {t : set α}
  (ht_m : m.is_measurable' t) :
  μ t = 0 ∨ μ t = 1 ∨ μ t = ⊤ :=
begin
  specialize h_indep t t ht_m ht_m,
  by_cases h0 : μ t = 0,
  { exact or.inl h0, },
  by_cases h_top : μ t = ⊤,
  { exact or.inr (or.inr h_top), },
  rw [←one_mul (μ (t ∩ t)), set.inter_self, ennreal.mul_eq_mul_right h0 h_top] at h_indep,
  exact or.inr (or.inl h_indep.symm),
end

lemma measure_eq_zero_or_one_of_indep_self {α} [measurable_space α] (μ : measure α)
  [finite_measure μ] {m : measurable_space α} (h_indep : @indep2 α m m _inst_1 μ) {t : set α}
  (ht_m : m.is_measurable' t) :
  μ t = 0 ∨ μ t = 1 :=
begin
  have h_0_1_top := @measure_eq_zero_or_one_or_top_of_indep_self α _inst_1 μ m h_indep t ht_m,
  cases h_0_1_top with h0 h_1_top,
  { exact or.inl h0, },
  cases h_1_top with h1 h_top,
  { exact or.inr h1, },
  exfalso,
  exact (@measure_ne_top α _inst_1 μ _ t) h_top,
end

lemma head_n_eq_generate_from_Union_Inter_range {α} (s : ℕ → measurable_space α) (n : ℕ):
  (⨆ i < n, s i) = measurable_space.generate_from
  (pi_system_Union_Inter (λ n, (s n).is_measurable') {finset.range n}) :=
begin
  rw ← Sup_prop_eq_generate_from_pi_system_Union_Inter s {finset.range n},
  simp,
end

lemma tail_n_eq_generate_from_Union_Inter_Ico {α} (s : ℕ → measurable_space α) (N : ℕ) :
  (⨆ i ≥ N, s i)
    = measurable_space.generate_from (pi_system_Union_Inter (λ n, (s n).is_measurable')
     {p : finset ℕ | ∃ r, p = finset.Ico N (N+r+1)}) :=
begin
  rw ←Sup_prop_eq_generate_from_pi_system_Union_Inter s
    {p : finset ℕ | ∃ r, p = finset.Ico N (N+r+1)},
  congr,
  ext1 i,
  have h_congr : i ≥ N
    = ∃ (p : finset ℕ) (hp : p ∈ {q : finset ℕ | ∃ r, q = finset.Ico N (N+r+1)}), i ∈ p,
  { rw eq_iff_iff,
    split; intro h,
    { use finset.Ico N (N+i+1),
      simp_rw [finset.Ico.mem, set.mem_set_of_eq],
      use i,
      refine ⟨h, _⟩,
      rw nat.lt_succ_iff,
      nth_rewrite 0 ←zero_add i,
      exact add_le_add_right (zero_le _) i, },
    simp_rw [exists_prop, set.mem_set_of_eq] at h,
    rcases h with ⟨p, ⟨r, hp⟩, hip⟩,
    rw [hp, finset.Ico.mem] at hip,
    exact hip.left, },
  congr,
  { exact h_congr, },
  ext1,
  { exact h_congr, },
  { exact (λ _ _ _, by refl), },
end

lemma range_ite {α} [comm_monoid α] (f : ℕ → α) (N : ℕ) :
  (∏ (x : ℕ) in finset.Ico 0 N, ite (x < N) (f x) 1) = ∏ (x : ℕ) in finset.Ico 0 N, (f x) :=
begin
  refine finset.prod_congr rfl (λ n hn, _),
  rw finset.Ico.mem at hn,
  simp [hn],
end

lemma aux_p1_product (f : ℕ → ennreal) (N r : ℕ) :
  (∏ (x : ℕ) in finset.range (N + r), ite (x < N) (f x) 1)
    = ∏ (x : ℕ) in finset.range N, (f x) :=
begin
  rw [←finset.Ico.zero_bot, ←finset.Ico.zero_bot],
  rw ←finset.prod_Ico_consecutive (λ x, ite (x < N) (f x) 1) (zero_le N),
  have h_left : (∏ i in finset.Ico 0 N, (λ (x : ℕ), ite (x < N) (f x) 1) i)
    = ∏ i in finset.Ico 0 N, f i,
  from range_ite f N,
  have h_right : (∏ i in finset.Ico N (N+r), (λ x, ite (x < N) (f x) 1) i) = 1,
  { have h_congr :
    (∏ i in finset.Ico N (N + r), (λ x, ite (x < N) (f x) 1) i)
      = (∏ i in finset.Ico N (N + r), 1),
    { refine finset.prod_congr rfl (λ x hx, _),
      simp_rw finset.Ico.mem at hx,
      have x_not_lt : ¬ x < N,
      { push_neg,
        exact hx.left, },
      simp [x_not_lt], },
    rw [h_congr, finset.prod_const_one], },
  rw [h_left, h_right, mul_one],
  { nth_rewrite 0 ←add_zero N,
    exact add_le_add_left (zero_le r) N, },
end

lemma prod_Ico_ite {α} [comm_monoid α] (N r : ℕ) (f : ℕ → α) :
  (∏ (n : ℕ) in finset.range (N + r), ite (N ≤ n ∧ n < N + r) (f n) 1)
    = ∏ (n : ℕ) in finset.Ico N (N + r), f n :=
begin
  rw ←finset.Ico.zero_bot,
  rw ←finset.prod_Ico_consecutive (λ x, ite (N ≤ x ∧ x < N + r) (f x) 1) (zero_le N),
  have h_left : (∏ (x : ℕ) in finset.range N, ite (N ≤ x ∧ x < N +r) (f x) 1) = 1,
  { refine finset.prod_eq_one (λ x hx, _),
    rw finset.mem_range at hx,
    have h_not : ¬ (N ≤ x ∧ x < N + r),
    { rw auto.not_and_eq,
      exact or.inl ((lt_iff_not_ge _ _).mp hx), },
    simp [h_not], },
  rw [finset.Ico.zero_bot, h_left, one_mul],
  refine finset.prod_congr rfl (λ x hx, _),
  rw finset.Ico.mem at hx,
  simp [hx],
  { nth_rewrite 0 ←add_zero N,
    exact add_le_add_left (zero_le r) N, },
end

lemma prod_range_offset {α} [comm_monoid α] (N r : ℕ) (f : ℕ → α) :
  (∏ (n : ℕ) in finset.range (N + r), ite (N ≤ n ∧ n < N + r) (f n) 1)
    = ∏ (n : ℕ) in finset.range r, f (N + n) :=
begin
  have h_sub : r = (N + r) - N, from (nat.add_sub_cancel_left N r).symm,
  nth_rewrite 1 h_sub,
  rw [prod_Ico_ite N r f, ←finset.prod_Ico_eq_prod_range],
end

lemma aux_p1_remove_ite (N r : ℕ) {p1 : finset ℕ} (f : ℕ → ennreal)
  (hp1 : p1 = finset.range N) :
  (∏ (x : ℕ) in finset.range (N + r + 1), ite (x ∈ p1) (f x) 1)
    = ∏ (x : ℕ) in finset.range N, (f x) :=
begin
  simp_rw [hp1, ←aux_p1_product (λ x, f x) N (r+1)],
  congr,
  simp,
end

lemma aux_p2_remove_ite (N r : ℕ) {p2 : finset ℕ} (f : ℕ → ennreal)
  (hp2 : p2 = finset.Ico N (N + r)) :
  (∏ (x : ℕ) in finset.range (N + r), ite (x ∈ p2) (f x) 1)
    = ∏ (x : ℕ) in finset.Ico N (N + r), f x :=
begin
  simp_rw [hp2, finset.Ico.mem],
  rw ←prod_Ico_ite N r f,
  --it looks like refl, but the `decidable` arguments of the ite are different.
  congr,
  ext1 n,
  congr,
end

lemma aux_t1_inter_t2 {α} (N r : ℕ) (f1 f2 : ℕ → set α) (p1 p2 : finset ℕ)
  (hp1 : p1 = finset.range N) (hp2 : p2 = finset.Ico N (N + r + 1)) :
  ((⋂ (i : ℕ) (hp : i ∈ p1), f1 i) ∩ ⋂ (i : ℕ) (hp : i ∈ p2), f2 i)
    = ⋂ (i : ℕ) (h_le : i ∈ finset.range (N + r + 1)),
      (ite (i ∈ p1) (f1 i) set.univ ∩ ite (i ∈ p2) (f2 i) set.univ) :=
begin
  rw finset.Inter_inter_Inter_eq_Inter_ite,
  have h_congr : p1 ∪ p2 = finset.range (N + r + 1),
  { rw [hp1, hp2, ←finset.Ico.zero_bot, ←finset.Ico.zero_bot],
    have h_le : N ≤ N + r + 1,
    { rw add_assoc,
      nth_rewrite 0 ←add_zero N,
      exact add_le_add_left (zero_le _) N, },
    rw ←finset.Ico.union_consecutive (zero_le N) h_le },
  congr,
  ext1 i,
  congr,
  { convert h_congr, },
  ext1 x,
  { congr', convert h_congr, },
  exact λ a a' haa', by congr',
end

lemma is_measurable.ite {α} [measurable_space α] {s t : set α} {p : Prop} (hs : p → is_measurable s)
  (ht : ¬p → is_measurable t)  :
  is_measurable (ite p s t) :=
begin
  split_ifs,
  exact hs h,
  exact ht h,
end

lemma head_n_indep_tail_n_pi_systems {α} [measurable_space α] (μ : measure α)
  [probability_measure μ] (s : ℕ → measurable_space α) (h_indep : indep s μ) (N : ℕ)
  (pi : ℕ → set (set α)) (hpis : pi = λ n, (s n).is_measurable') :
  indep2_sets (pi_system_Union_Inter pi {finset.range N})
    (pi_system_Union_Inter pi {p : finset ℕ | ∃ r : ℕ, p = finset.Ico N (N+r+1)}) μ :=
begin
  intros t1 t2 ht1 ht2,
  rcases ht1 with ⟨p1, hp1, f1, ht1_m, ht1_eq⟩,
  rcases ht2 with ⟨p2, hp2, f2, ht2_m, ht2_eq⟩,
  rw set.mem_singleton_iff at hp1,
  cases hp2 with r hp2,
  let g := λ i, ite (i ∈ p1) (f1 i) set.univ ∩ ite (i ∈ p2) (f2 i) set.univ,
  have hf1m : ∀ (n : ℕ), n ∈ p1 → (s n).is_measurable' (f1 n), by rwa hpis at ht1_m,
  have hf2m : ∀ (n : ℕ), n ∈ p2 → (s n).is_measurable' (f2 n), by rwa hpis at ht2_m,
  have h_P_inter : μ (t1 ∩ t2) = ∏ n in finset.range (N+r+1), μ (g n),
  { have hgm : ∀ i, i ∈ finset.range (N + r + 1) → (s i).is_measurable' (g i),
    { refine (λ i _, @is_measurable.inter α (s i) _ _ _ _),
      { convert @is_measurable.ite α (s i) _ _ _ (hf1m i) (λ _, @is_measurable.univ α (s i)), },
      { convert @is_measurable.ite α (s i) _ _ _ (hf2m i) (λ _, @is_measurable.univ α (s i)), }, },
    rw [ht1_eq, ht2_eq, aux_t1_inter_t2 N r f1 f2 p1 p2 hp1 hp2],
    have h_almost := h_indep (finset.range (N+r+1)) hgm,
    dsimp only at h_almost,
    rw ←h_almost, },
  rw h_P_inter,
  have h_μg : ∀ n, μ (g n) = (ite (n ∈ p1) (μ (f1 n)) 1) * (ite (n ∈ p2) (μ (f2 n)) 1),
  { intro n,
    change μ (ite (n ∈ p1) (f1 n) set.univ ∩ ite (n ∈ p2) (f2 n) set.univ)
      = ite (n ∈ p1) (μ (f1 n)) 1 * ite (n ∈ p2) (μ (f2 n)) 1,
    split_ifs,
    { exfalso,
      rw [hp1, finset.mem_range] at h,
      rw [hp2, finset.Ico.mem] at h_1,
      linarith, },
    all_goals { simp [measure_univ], }, },
  simp_rw h_μg,
  have h1 : (∏ (x : ℕ) in finset.range (N + r + 1), ite (x ∈ p1) (μ (f1 x)) 1)
    = ∏ (x : ℕ) in finset.range N, μ (f1 x),
  from aux_p1_remove_ite N r (λ n, μ (f1 n)) hp1,
  have h2 : (∏ (x : ℕ) in finset.range (N + r + 1), ite (x ∈ p2) (μ (f2 x)) 1)
    = ∏ (x : ℕ) in finset.Ico N (N + r + 1), μ (f2 x),
  from aux_p2_remove_ite N (r + 1) (λ n, μ (f2 n)) hp2,
  have h_P_1 : μ t1 = ∏ n in p1, μ (f1 n), by rw [ht1_eq, ←h_indep p1 hf1m],
  have h_P_2 : μ t2 = ∏ n in p2, μ (f2 n), by rw [ht2_eq, ←h_indep p2 hf2m],
  rw [finset.prod_mul_distrib, h1, h2, h_P_1, h_P_2],
  simp_rw [hp1, hp2],
end

lemma head_n_indep_tail_n {α} {m : measurable_space α} (μ : measure α) [probability_measure μ]
  (s : ℕ → measurable_space α) (h_le : ∀ n, s n ≤ m) (h_indep : indep s μ) (N : ℕ) :
  indep2 (⨆ n < N, s n) (⨆ i ≥ N, s i) μ :=
begin
  -- define a π-system family
  have h_pi : ∀ n, is_pi_system ((s n).is_measurable'),
  from (λ n, @measurable_space.is_pi_system_is_measurable α (s n)),
  -- define generating π-systems for head and tail
  let p_head := pi_system_Union_Inter (λ n, (s n).is_measurable') {finset.range N},
  have h_pi_head : is_pi_system p_head,
  from is_pi_system_pi_system_Union_Inter (λ n, (s n).is_measurable') h_pi {finset.range N}
    (by convert sup_closed_singleton (finset.range N)),
  have h_generate_head : (⨆ n < N, s n) = measurable_space.generate_from p_head,
  from head_n_eq_generate_from_Union_Inter_range s N,
  let S_tail := {p : finset ℕ | ∃ r : ℕ, p = finset.Ico N (N+r+1)},
  let p_tail := pi_system_Union_Inter (λ n, (s n).is_measurable') S_tail,
  have h_pi_tail : is_pi_system p_tail,
  from is_pi_system_pi_system_Union_Inter (λ n, (s n).is_measurable') h_pi S_tail
    (by convert sup_closed_tail_finset_set N),
  have h_generate_tail : (⨆ i ≥ N, s i) = measurable_space.generate_from p_tail,
  from tail_n_eq_generate_from_Union_Inter_Ico s N,
  -- if these π-systems are indep, head and tail are indep
  refine indep2_of_indep2_sets_of_pi_system (head_n_le s N h_le) (tail_n_le s N h_le)
    h_pi_head h_pi_tail h_generate_head h_generate_tail _,
  exact head_n_indep_tail_n_pi_systems μ s h_indep N (λ n, (s n).is_measurable') rfl,
end

lemma head_n_indep_tail {α} {m : measurable_space α} (μ : measure α) [probability_measure μ]
  (s : ℕ → measurable_space α) (h_le : ∀ n, s n ≤ m) (h_indep : indep s μ) (n : ℕ) :
  indep2 (⨆ i < n, s i) (tail s) μ :=
indep2.symm (indep2_of_indep2_of_le_left (indep2.symm (head_n_indep_tail_n μ s h_le h_indep n))
  (tail_le_tail_n s n))

lemma generate_from_supr_generate_from {α} {ι : Type} (s : ι → set (set α)) :
  (⨆ n, measurable_space.generate_from (s n))
    = measurable_space.generate_from (⨆ n, (measurable_space.generate_from (s n)).is_measurable') :=
((@measurable_space.gi_generate_from α).l_supr_u (λ n, measurable_space.generate_from (s n))).symm

lemma supr_eq_generate_from_Union_head_n {α} (s : ℕ → measurable_space α) :
  supr s = measurable_space.generate_from (⋃ n, (⨆ i < n, s i).is_measurable') :=
begin
  rw supr_eq_supr_head_n,
  have h_eq : ∀ n, (⨆ i < n, s i) = measurable_space.generate_from ((⨆ i < n, s i).is_measurable'),
  from (λ n,(@measurable_space.generate_from_is_measurable α (⨆ i < n, s i)).symm),
  have h_left : (⨆ n, ⨆ i < n, s i)
    = ⨆ n, measurable_space.generate_from ((⨆ i < n, s i).is_measurable'),
  { congr,
    ext1 n,
    exact h_eq n, },
  rw [h_left, generate_from_supr_generate_from (λ n : ℕ, (⨆ i < n, s i).is_measurable')],
  congr,
  ext1 n,
  rw ←h_eq n,
end

lemma is_pi_system_monotone_Union {α} (p : ℕ → set (set α)) (hp_pi : ∀ n, is_pi_system (p n))
  (hp_mono : ∀ n m : ℕ, n ≤ m → p n ⊆ p m) :
  is_pi_system (⋃ n, p n) :=
begin
  intros t1 t2 ht1 ht2 h,
  rw set.mem_Union at ht1 ht2 ⊢,
  cases ht1 with n ht1,
  cases ht2 with m ht2,
  by_cases h_le : n ≤ m,
  { use m,
    have ht1' : t1 ∈ p m, from set.mem_of_mem_of_subset ht1 (hp_mono n m h_le),
    exact hp_pi m t1 t2 ht1' ht2 h, },
  { use n,
    push_neg at h_le,
    have ht2' : t2 ∈ p n, from set.mem_of_mem_of_subset ht2 (hp_mono m n (le_of_lt h_le)),
    exact hp_pi n t1 t2 ht1 ht2' h, },
end

lemma supr_indep_tail {α} {m : measurable_space α} (μ : measure α) [probability_measure μ]
  (s : ℕ → measurable_space α) (h_le : ∀ n, s n ≤ m) (h_indep : indep s μ) :
  indep2 (⨆ n, s n) (tail s) μ :=
begin
  let p : ℕ → set (set α) := λ n, (⨆ i < n, s i).is_measurable',
  have hp : ∀ n, is_pi_system (p n),
  from λ n, @measurable_space.is_pi_system_is_measurable α (⨆ i < n, s i),
  have h_generate_n : ∀ n, (⨆ i < n, s i) = measurable_space.generate_from (p n),
  from λ n, (@measurable_space.generate_from_is_measurable α (⨆ i < n, s i)).symm,
  have hp_mono : ∀ n m, n ≤ m → p n ⊆ p m, from (λ n m hnm, head_n_mono s hnm),
  have h_pi : is_pi_system (⋃ n, p n), from is_pi_system_monotone_Union p hp hp_mono,
  let p' := {t : set α | (tail s).is_measurable' t},
  have hp'_pi : is_pi_system p', from @measurable_space.is_pi_system_is_measurable α (tail s),
  have h_generate' : tail s = measurable_space.generate_from p',
  from (@measurable_space.generate_from_is_measurable α (tail s)).symm,
  -- the π-systems defined are independent
  have h_indep_n : ∀ n, indep2_sets (p n) p' μ,
  { intro n,
    have h_sigma_indep : indep2 (⨆ i < n, s i) (tail s) μ,
    from head_n_indep_tail μ s h_le h_indep n,
    rw [h_generate_n n, h_generate'] at h_sigma_indep,
    exact indep2_sets_of_indep2 h_sigma_indep, },
  have h_pi_system_indep : indep2_sets (⋃ n, p n) p' μ, from indep2_sets.Union h_indep_n,
  -- now go from π-systems to σ-algebras
  refine indep2_of_indep2_sets_of_pi_system (supr_le h_le) (tail_le h_le) h_pi hp'_pi
    (supr_eq_generate_from_Union_head_n s) h_generate' h_pi_system_indep,
end

lemma tail_indep_tail {α} {m : measurable_space α} {μ : measure α} [probability_measure μ]
  {s : ℕ → measurable_space α} (h_le : ∀ n, s n ≤ m) (h_indep : indep s μ) :
  indep2 (tail s) (tail s) μ :=
indep2_of_indep2_of_le_left (supr_indep_tail μ s h_le h_indep)
    (le_trans (tail_le_tail_n s 0) (tail_n_le_supr s 0))

/-- Kolmogorov 0-1 law : any event in the tail σ-algebra has probability 0 or 1 -/
theorem zero_or_one_of_tail {α} {m : measurable_space α} (μ : measure α) [probability_measure μ]
  {s : ℕ → measurable_space α} (h_le : ∀ n, s n ≤ m) (h_indep : indep s μ) {t : set α}
  (h_t_tail : (tail s).is_measurable' t) :
  (μ t = 0 ∨ μ t = 1) :=
measure_eq_zero_or_one_of_indep_self μ (tail_indep_tail h_le h_indep) h_t_tail

end zero_one_law
