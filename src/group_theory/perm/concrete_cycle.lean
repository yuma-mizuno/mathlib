import group_theory.perm.list
import data.list.cycle
import group_theory.perm.cycle_type

open equiv equiv.perm list

lemma nat.lt_one_iff {n : ℕ} :
  n < 1 ↔ n = 0 :=
⟨λ h, le_antisymm (nat.le_of_lt_succ h) n.zero_le, λ h, nat.lt_succ_of_le h.le⟩

namespace list

variables {α : Type*} [decidable_eq α] {l l' : list α}

lemma form_perm_disjoint_iff (hl : nodup l) (hl' : nodup l')
  (hn : 2 ≤ l.length) (hn' : 2 ≤ l'.length) :
  perm.disjoint (form_perm l) (form_perm l') ↔ l.disjoint l' :=
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

lemma form_perm_apply_mem_eq_next (hl : nodup l) (x : α) (hx : x ∈ l) :
  form_perm l x = next l x hx :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  rw [next_nth_le _ hl, form_perm_apply_nth_le _ hl]
end

end list

namespace cycle

variables {α : Type*} [decidable_eq α] (s s' : cycle α)

/--
A cycle `s : cycle α` , given `nodup s` can be interpreted as a `equiv.perm α`
where each element in the list is permuted to the next one, defined as `form_perm`.
-/
def form_perm : Π (s : cycle α) (h : nodup s), equiv.perm α :=
λ s, quot.hrec_on s (λ l h, form_perm l)
  (λ l₁ l₂ (h : l₁ ~r l₂),
    begin
      ext,
      { exact h.nodup_iff },
      { intros h₁ h₂ _,
        refine heq_of_eq _,
        exact form_perm_eq_of_is_rotated h₁ h }
    end)

@[simp] lemma form_perm_coe (l : list α) (hl : l.nodup) :
  form_perm (l : cycle α) hl = l.form_perm := rfl

lemma form_perm_subsingleton (s : cycle α) (h : subsingleton s) :
  form_perm s h.nodup = 1 :=
begin
  induction s using quot.induction_on,
  simp only [form_perm_coe, mk_eq_coe],
  simp only [length_subsingleton_iff, length_coe, mk_eq_coe] at h,
  cases s with hd tl,
  { simp },
  { simp only [length_eq_zero, add_le_iff_nonpos_left, list.length, nonpos_iff_eq_zero] at h,
    simp [h] }
end

lemma is_cycle_form_perm (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  is_cycle (form_perm s h) :=
begin
  induction s using quot.induction_on,
  exact list.is_cycle_form_perm h (length_nontrivial hn)
end

lemma support_form_perm [fintype α] (s : cycle α) (h : nodup s) (hn : nontrivial s) :
  support (form_perm s h) = s.to_finset :=
begin
  induction s using quot.induction_on,
  refine support_form_perm_of_nodup s h _,
  rintro _ rfl,
  simpa [nat.succ_le_succ_iff] using length_nontrivial hn
end

lemma form_perm_apply_not_mem (s : cycle α) (h : nodup s) (x : α) (hx : x ∉ s) :
  form_perm s h x = x :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_apply_not_mem _ _ hx
end

lemma form_perm_apply_mem (s : cycle α) (h : nodup s) (x : α) (hx : x ∈ s) :
  form_perm s h x = next s h x hx :=
begin
  induction s using quot.induction_on,
  simpa using list.form_perm_apply_mem_eq_next h _ _
end

lemma form_perm_reverse (s : cycle α) (h : nodup s) :
  form_perm s.reverse (nodup_reverse_iff.mpr h) = (form_perm s h)⁻¹ :=
begin
  induction s using quot.induction_on,
  simpa using form_perm_reverse _ h
end

end cycle

variables {α : Type*}

def list.iterate (f : α → α) : α → ℕ → list α
| x 0       := []
| x (n + 1) := x :: list.iterate (f x) n

-- def perm.to_list' (p : equiv.perm α) (x : α) (k : ℕ) : list α :=
-- list.iterate p x k

lemma equiv.perm.is_cycle.exists_pow_pos {p : equiv.perm α} (hp : is_cycle p) (x : α) :
  ∃ (n : ℕ) (hn : 0 < n), (p ^ n) x = x :=
begin
  by_cases hx : p x = x,
  { use 1,
    simp [hx] },
  by_cases hx' : p (p x) = x,
  { use 2,
    simp [pow_succ, hx'] },
  { obtain ⟨n, hn⟩ := hp.exist_pow_eq hx hx', },
  -- use order_of p,
  -- simp [pow_order_of_eq_one],
  -- refine order_of_pos' _,
  -- obtain ⟨n, hn⟩ := hp.exists_gpow_eq hx hx,
  -- {
  --   -- obtain ⟨y, hy, hy'⟩ := id hp,
  --   use (order_of p - 1),
  --   rw nat.sub_add_cancel,
  --   rw pow_order_of_eq_one,
  --   -- simp [pow_succ'],
  --   -- rw pow_order_of_eq_one,
  --   -- use n,
  --   -- simp [pow_succ, ←hn],
  -- },
end

-- def perm.to_list (p : equiv.perm α) (hp : is_cycle p) (x : α) : list α :=
-- list.iterate p x (nat.find (_ : ∃ (n : ℕ), (p ^ n) x = x))
