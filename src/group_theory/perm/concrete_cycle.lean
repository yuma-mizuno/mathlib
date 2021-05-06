import group_theory.perm.list
import group_theory.perm.cycle_type

variables {α : Type*} [decidable_eq α] {l l' : list α}

open equiv equiv.perm list

lemma nat.lt_one_iff {n : ℕ} :
  n < 1 ↔ n = 0 :=
⟨λ h, le_antisymm (nat.le_of_lt_succ h) n.zero_le, λ h, nat.lt_succ_of_le h.le⟩

lemma form_perm_disjoint_iff (hl : nodup l) (hl' : nodup l')
  (hn : 2 ≤ l.length) (hn' : 2 ≤ l'.length) :
  disjoint (form_perm l) (form_perm l') ↔ l.disjoint l' :=
begin
  rw disjoint_iff_eq_or_eq,
  rw list.disjoint,
  split,
  { rintro h x hx hx',
    specialize h x,
    rw [form_perm_apply_mem_eq_self_iff _ hl _ hx,
        form_perm_apply_mem_eq_self_iff _ hl' _ hx',
        le_iff_eq_or_lt, le_iff_eq_or_lt, nat.lt_one_iff, nat.lt_one_iff,
        length_eq_one, length_eq_one, length_eq_zero, length_eq_zero] at h,
    rcases h with (⟨hd, rfl⟩|rfl)|(⟨hd, rfl⟩|rfl);
    simpa using hx <|> simpa using hx' <|>
      simpa [nat.succ_le_succ_iff] using hn <|> simpa [nat.succ_le_succ_iff] using hn' },
  { intros h x,
    by_cases hx : x ∈ l;
    by_cases hx' : x ∈ l',
    { simpa using h hx hx' },
    { simp [form_perm_not_mem_apply _ _ hx'] },
    { simp [form_perm_not_mem_apply _ _ hx] },
    { simp [form_perm_not_mem_apply _ _ hx'] } }
end

lemma is_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  is_cycle (form_perm l) :=
begin
  cases l with x l,
  { simpa using hn },
  induction l with y l IH generalizing x,
  { simpa [nat.succ_le_succ_iff] using hn },
  { use x,
    split,
    { rwa form_perm_apply_mem_ne_self_iff _ hl _ (mem_cons_self _ _) },
    { intros w hw,
      have : w ∈ (x :: y :: l) := form_perm_ne_self_imp_mem _ _ hw,
      obtain ⟨k, hk, rfl⟩ := nth_le_of_mem this,
      use k,
      rw gpow_coe_nat,
      convert form_perm_pow_apply_nth_le _ hl k 0 (by simp),
      rw [nat.zero_add, nat.mod_eq_of_lt hk] } }
end

lemma pairwise_same_cycle_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  pairwise (l.form_perm.same_cycle) l :=
begin
  rw pairwise.imp_mem,
  refine pairwise_of_forall _,
  intros x y hx hy,
  refine (is_cycle_form_perm hl hn).same_cycle _ _;
  { rwa form_perm_apply_mem_ne_self_iff _ hl _,
    assumption }
end

lemma cycle_of_form_perm (hl : nodup l) (hn : 2 ≤ l.length) (x) :
  cycle_of l.attach.form_perm x = l.attach.form_perm :=
begin
  rw ←length_attach at hn,
  rw ←nodup_attach at hl,
  refine is_cycle.cycle_of_eq _ _,
  { exact is_cycle_form_perm hl hn },
  { rwa form_perm_apply_mem_ne_self_iff _ hl,
    exact mem_attach _ _ }
end

lemma cycle_type_form_perm (hl : nodup l) (hn : 2 ≤ l.length) :
  cycle_type l.attach.form_perm = {l.length} :=
begin
  rw ←length_attach at hn,
  rw ←nodup_attach at hl,
  rw cycle_type_eq [l.attach.form_perm],
  { simp only [multiset.singleton_eq_singleton, map, function.comp_app],
    rw [support_form_perm_of_nodup _ hl, card_to_finset, erase_dup_eq_self.mpr hl],
    { simpa },
    { intros x h,
      simpa [h, nat.succ_le_succ_iff] using hn } },
  { simp },
  { simpa using is_cycle_form_perm hl hn },
  { simp }
end
