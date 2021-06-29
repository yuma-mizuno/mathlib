/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.cycle
import group_theory.perm.support

/-!
# Permutations from a list

A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.

-/

lemma nat.lt_one_iff {n : ℕ} :
  n < 1 ↔ n = 0 :=
⟨λ h, le_antisymm (nat.le_of_lt_succ h) n.zero_le, λ h, nat.lt_succ_of_le h.le⟩

namespace list

variables {α β : Type*}

lemma not_mem_imp_ne_last {l : list α} {x : α} (hx : x ∉ l) (hl : l ≠ []) :
  x ≠ l.last hl :=
begin
  induction l with hd tl IH,
  { contradiction },
  { simp only [not_or_distrib, mem_cons_iff] at hx,
    cases tl,
    { simpa using hx.left },
    { simpa using IH hx.right _ } }
end

section form_perm

variables [decidable_eq α] (l : list α)

open equiv equiv.perm

/--
A list `l : list α` can be interpreted as a `equiv.perm α` where each element in the list
is permuted to the next one, defined as `form_perm`. When we have that `nodup l`,
we prove that `equiv.perm.support (form_perm l) = l.to_finset`, and that
`form_perm l` is rotationally invariant, in `form_perm_rotate`.
-/
def form_perm : equiv.perm α :=
(zip_with equiv.swap l (l.rotate 1)).tail.prod

@[simp] lemma form_perm_nil : form_perm ([] : list α) = 1 := rfl

@[simp] lemma form_perm_singleton (x : α) : form_perm [x] = 1 := rfl

@[simp] lemma form_perm_pair (x y : α) : form_perm [x, y] = swap y x := rfl

lemma form_perm_cons_cons_cons (x y z : α) (xs : list α) :
  form_perm (x :: y :: z :: xs) = swap y z * form_perm (x :: z :: xs) :=
begin
  cases xs with w xs,
  { simp [form_perm] },
  { rw [form_perm, zip_with_rotate_one, tail_cons, cons_append, zip_with_cons_cons,
        ←tail_cons x (z :: w :: xs), ←tail_cons z (w :: xs ++ [x]),
        ←rotate_zero (z :: (w :: xs ++ [x])), ←cons_append, ←rotate_cons_succ,
        ←zip_with_distrib_tail, prod_cons, ←form_perm, tail_cons] }
end

-- lemma form_perm_apply_eq_iff (xs : list α) (x y : α) :
--   form_perm xs x = y ↔ (x ∉ xs ∧ x = y) ∨ (∃ h : x ∈ xs, y = next xs x h) :=
-- begin
--   cases xs with a xs,
--   { simp },
--   cases xs with b xs,
--   { by_cases hx : x = a,
--     { simp [hx, eq_comm] },
--     { simp [hx] } },
--   induction xs with c xs IH generalizing x y a b,
--   { simp only [mem_cons_iff, form_perm_pair, mem_singleton],
--     by_cases ha : x = a,
--     { simp [ha, eq_comm] },
--     by_cases hb : x = b,
--     { by_cases hab : a = b;
--       simp [hb, hab, next, eq_comm] },
--     { simp [swap_apply_of_ne_of_ne, ha, hb] } },
--   { rw form_perm_cons_cons_cons,
--     simp only [mem_cons_iff, coe_mul, function.comp_app],
--     rw apply_eq_iff_eq_symm_apply,
--     rw IH,
--     rw ←apply_eq_iff_eq_symm_apply,
--     simp only [mem_cons_iff, symm_swap, not_or_distrib],
--     split,
--     { rintro (⟨⟨ha, hc, hm⟩, rfl⟩ | ⟨hm, h⟩),
--       { by_cases hb : x = b,
--         { subst hb,
--           refine or.inr ⟨_, _⟩,
--           { simp },
--           { rw next_ne_head_ne_last _ _ _ _ ha,
--             { simp },
--             { simp only [last, ne.def],
--               refine not_mem_imp_ne_last _ _,
--               simp [not_or_distrib, hc, hm] } } },
--         { simp [ha, hb, hc, hm, swap_apply_of_ne_of_ne] } },
--       { simp only [mem_cons_iff] at hm,
--         by_cases ha : x = a,
--         { simpa [ha, swap_apply_eq_iff] using h },
--         by_cases hc : x = c,
--         { subst hc,
--           by_cases hb : y = b,
--           { simp only [hb, next, ha, swap_apply_left, last_cons_cons, last, dif_neg,
--                        not_false_iff] at h,
--             split_ifs at h with h' h',
--             { contradiction },
--             { simp [hb], },
--             simp,
--           },
--           {  },
--           },
--         -- rw swap_apply_eq_iff at h,
--         -- rcases hm with rfl|rfl|hm,
--         -- { simpa using h },
--         -- {
--         --   simp,
--         --   sorry,
--         --   },
--         -- { simp [hm], },
--         -- simp [h],
--       },
--     },
--     {  },
--   },
-- end

lemma form_perm_apply_last_concat (x y : α) (xs : list α) (h : nodup (x :: (xs ++ [y]))) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  cases xs with z xs,
  { simp },
  induction xs with w xs IH generalizing x y z,
  { simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
               nodup_cons, not_false_iff, and_self, mem_singleton] at h,
    push_neg at h,
    simp [form_perm, swap_apply_of_ne_of_ne, h] },
  { simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
               nodup_cons, not_false_iff, and_self, mem_singleton] at h,
    push_neg at h,
    simp_rw [cons_append],
    rw [form_perm_cons_cons_cons, mul_apply, ←cons_append, IH],
    { simp [swap_apply_of_ne_of_ne, h] },
    { simp [h] } }
end

lemma form_perm_apply_last (x : α) (xs : list α) (h : nodup (x :: xs)) :
  form_perm (x :: xs) ((x :: xs).last (cons_ne_nil x xs)) = x :=
begin
  induction xs using list.reverse_rec_on with xs y IH generalizing x,
  { simp },
  { simpa using form_perm_apply_last_concat x y xs h }
end

lemma form_perm_apply_nth_le_length (x : α) (xs : list α) (h : nodup (x :: xs)) :
  form_perm (x :: xs) ((x :: xs).nth_le xs.length (by simp)) = x :=
begin
  rw nth_le_cons_length,
  exact form_perm_apply_last x xs h
end

@[simp] lemma form_perm_apply_head (x y : α) (xs : list α) :
  form_perm (x :: y :: xs) x = y :=
begin
  induction xs with z xs IH generalizing x y,
  { simp },
  { rw [form_perm_cons_cons_cons, mul_apply, IH, swap_apply_right] }
end

lemma form_perm_apply_concat (x y : α) (xs : list α) (h : nodup (x :: (xs ++ [y]))) :
  form_perm (x :: (xs ++ [y])) y = x :=
begin
  convert form_perm_apply_last x (xs ++ [y]) h,
  simp
end

lemma zip_with_swap_prod_support' (l l' : list α) :
  {x | (zip_with swap l l').prod x ≠ x} ≤ l.to_finset ⊔ l'.to_finset :=
begin
  simp only [set.sup_eq_union, set.le_eq_subset],
  induction l with y l hl generalizing l',
  { simp },
  { cases l' with z l',
    { simp },
    { intro x,
      simp only [set.union_subset_iff, mem_cons_iff, zip_with_cons_cons, foldr, prod_cons,
                 mul_apply],
      intro hx,
      by_cases h : x ∈ {x | (zip_with swap l l').prod x ≠ x},
      { specialize hl l' h,
        refine set.mem_union.elim hl (λ hm, _) (λ hm, _);
        { simp only [finset.coe_insert, set.mem_insert_iff, finset.mem_coe, to_finset_cons,
                     mem_to_finset] at hm ⊢,
          simp [hm] } },
      { simp only [not_not, set.mem_set_of_eq] at h,
        simp only [h, set.mem_set_of_eq] at hx,
        rw swap_apply_ne_self_iff at hx,
        rcases hx with ⟨hyz, rfl|rfl⟩;
        simp } } }
end

lemma zip_with_swap_prod_support [fintype α] (l l' : list α) :
  (zip_with swap l l').prod.support ≤ l.to_finset ⊔ l'.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | (zip_with swap l l').prod x ≠ x} := by simpa using hx,
  simpa using zip_with_swap_prod_support' _ _ hx'
end

lemma support_form_perm_le' : {x | form_perm l x ≠ x} ≤ l.to_finset :=
begin
  rw [form_perm, zip_with_distrib_tail],
  refine (zip_with_swap_prod_support' l.tail _).trans _,
  rintro x (hx | hx),
  { simp only [finset.mem_coe, mem_to_finset] at hx ⊢,
    exact tail_subset _ hx },
  { simp only [finset.mem_coe, mem_to_finset] at hx ⊢,
    refine (list.subset.trans (tail_subset _) (perm.subset _)) hx,
    exact rotate_perm l 1 }
end

lemma support_form_perm_le [fintype α] : support (form_perm l) ≤ l.to_finset :=
begin
  intros x hx,
  have hx' : x ∈ {x | form_perm l x ≠ x} := by simpa using hx,
  simpa using support_form_perm_le' _ hx'
end

lemma form_perm_not_mem_apply (x : α) (l : list α) (h : x ∉ l) :
  form_perm l x = x :=
begin
  have : x ∉ {x | form_perm l x ≠ x},
    { intro H,
      refine h _,
      simpa using support_form_perm_le' l H },
  simpa
end

lemma form_perm_ne_self_imp_mem (x : α) (l : list α) (h : form_perm l x ≠ x) :
  x ∈ l :=
begin
  contrapose! h,
  exact form_perm_not_mem_apply x l h
end

lemma form_perm_mem_apply_imp_mem (x : α) (l : list α) (h : x ∈ l) :
  form_perm l x ∈ l :=
begin
  by_cases hl : form_perm l x = x,
  { simpa [hl] using h },
  { have hl' : x ∈ {x | form_perm l x ≠ x} := hl,
    rw [←set_support_apply_mem, set.mem_set_of_eq] at hl',
    exact form_perm_ne_self_imp_mem _ _ hl' }
end

lemma form_perm_apply_lt (xs : list α) (h : nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
  form_perm xs (xs.nth_le n ((nat.lt_succ_self n).trans hn)) = xs.nth_le (n + 1) hn :=
begin
  induction n with n IH generalizing xs,
  { cases xs with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    { simp } },
  { cases xs with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    cases xs with z xs,
    { simpa [nat.succ_lt_succ_iff] using hn },
    { rw [form_perm_cons_cons_cons],
      simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
                nodup_cons, not_false_iff, and_self, mem_singleton] at h,
      push_neg at h,
      cases n,
      { have : y ∉ (x :: z :: xs),
        { simp [h, h.left.left.symm] },
        simp [form_perm_not_mem_apply _ _ this] },
      { rw [mul_apply],
        have : ∀ (hz), (x :: y :: z :: xs).nth_le n.succ.succ hz =
          (x :: z :: xs).nth_le n.succ (by simpa [nat.succ_lt_succ_iff] using hz),
          { simp },
        have hn' : n.succ + 1 < (x :: z :: xs).length,
          { simpa [nat.succ_lt_succ_iff] using hn },
        rw [this, IH _ _ hn', swap_apply_of_ne_of_ne],
        { simp },
        { have : y ∉ xs := by simp [h],
          simp only [ne.def, nth_le],
          rintro rfl,
          exact this (nth_le_mem _ _ _) },
        { have : z ∉ xs := by simp [h],
          simp only [ne.def, nth_le],
          intro hz,
          rw [←hz] at this,
          exact this (nth_le_mem _ _ _) },
        { simp [h] } } } }
end

-- useful for rewrites
lemma form_perm_apply_lt' (xs : list α) (h : nodup xs) (x : α) (n : ℕ) (hn : n + 1 < xs.length)
  (hx : x = (xs.nth_le n ((nat.lt_succ_self n).trans hn))) :
  (form_perm xs) x = xs.nth_le (n + 1) hn :=
by { rw hx, exact form_perm_apply_lt _ h _ _ }

lemma form_perm_apply_nth_le (xs : list α) (h : nodup xs) (n : ℕ) (hn : n < xs.length) :
  form_perm xs (xs.nth_le n hn) = xs.nth_le ((n + 1) % xs.length)
    (nat.mod_lt _ (n.zero_le.trans_lt hn)) :=
begin
  cases xs with x xs,
  { simp },
  { have : n ≤ xs.length,
      { refine nat.le_of_lt_succ _,
        simpa using hn },
    rcases this.eq_or_lt with rfl|hn',
    { simp [form_perm_apply_nth_le_length _ _ h] },
    { simp [form_perm_apply_lt, h, nat.mod_eq_of_lt, nat.succ_lt_succ hn'] } }
end

-- useful for rewrites
lemma form_perm_apply_nth_le' (xs : list α) (h : nodup xs) (x : α) (n : ℕ) (hn : n < xs.length)
  (hx : x = xs.nth_le n hn) :
  form_perm xs x = xs.nth_le ((n + 1) % xs.length)
    (by { cases xs, { simpa using hn }, { refine nat.mod_lt _ _, simp }}) :=
by { simp_rw hx, exact form_perm_apply_nth_le _ h _ _ }

lemma support_form_perm_of_nodup' (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  {x | form_perm l x ≠ x} = l.to_finset :=
begin
  apply le_antisymm,
  { exact support_form_perm_le' l },
  { intros x hx,
    simp only [finset.mem_coe, mem_to_finset] at hx,
    obtain ⟨n, hn, rfl⟩ := nth_le_of_mem hx,
    cases l with x xs,
    { simpa using hn },
    cases xs with y xs,
    { simpa using h' x },
    { have nle : n ≤ (y :: xs).length,
        { refine nat.le_of_lt_succ _,
          simpa using hn },
      simp,
      rcases nle.eq_or_lt with rfl|hn',
      { rw form_perm_apply_nth_le_length _ _ h,
        simp only [mem_cons_iff, cons_append, nodup_nil, and_true, not_mem_nil, singleton_append,
                   nodup_cons, not_false_iff, and_self, mem_singleton] at h,
        push_neg at h,
        have : x ∉ (y :: xs) := by simp [h],
        simp only [length, ne.def, nth_le],
        intro hx,
        rw [hx] at this,
        exact this (nth_le_mem _ _ _) },
      { have nsle : n + 1 < (x :: y :: xs).length,
          { simpa using hn' },
        rw [form_perm_apply_lt _ h n nsle],
        intro H,
        exact nth_le_eq_of_ne_imp_not_nodup _ _ _ _ _ H (nat.lt_succ_self n).ne' h } } }
end

lemma support_form_perm_of_nodup [fintype α] (l : list α) (h : nodup l) (h' : ∀ (x : α), l ≠ [x]) :
  support (form_perm l) = l.to_finset :=
begin
  rw ←finset.coe_inj,
  convert support_form_perm_of_nodup' _ h h',
  simp [set.ext_iff]
end

lemma form_perm_rotate_one (l : list α) (h : nodup l) :
  form_perm (l.rotate 1) = form_perm l :=
begin
  have h' : nodup (l.rotate 1),
    { simpa using h },
  by_cases hl : ∀ (x : α), l ≠ [x],
  { have hl' : ∀ (x : α), l.rotate 1 ≠ [x],
      { intro,
        rw [ne.def, rotate_eq_iff],
        simpa using hl _ },
    ext x,
    by_cases hx : x ∈ l.rotate 1,
    { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
      rw form_perm_apply_nth_le' _ h' _ k hk rfl,
      simp_rw nth_le_rotate l,
      rw form_perm_apply_nth_le' _ h,
      { simp },
      { cases l,
        { simpa using hk },
        { simpa using nat.mod_lt _ nat.succ_pos' } } },
    { rw [form_perm_not_mem_apply _ _ hx, form_perm_not_mem_apply],
      simpa using hx } },
  { push_neg at hl,
    obtain ⟨x, rfl⟩ := hl,
    simp }
end

lemma form_perm_rotate (l : list α) (h : nodup l) (n : ℕ) :
  form_perm (l.rotate n) = form_perm l :=
begin
  induction n with n hn,
  { simp },
  { rw [nat.succ_eq_add_one, ←rotate_rotate, form_perm_rotate_one, hn],
    rwa is_rotated.nodup_iff,
    exact is_rotated.forall l n }
end

lemma form_perm_eq_of_is_rotated {l l' : list α} (hd : nodup l) (h : l ~r l') :
  form_perm l = form_perm l' :=
begin
  obtain ⟨n, rfl⟩ := h,
  exact (form_perm_rotate l hd n).symm
end

lemma form_perm_reverse (l : list α) (h : nodup l) :
  form_perm l.reverse = (form_perm l)⁻¹ :=
begin
  ext x,
  by_cases hx : x ∈ l,
  { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
    cases l with x xs,
    { simp },
    cases xs with y xs,
    { simp },
    rw [form_perm_apply_nth_le' _ _ _ ((x :: y :: xs).length - 1 - k), nth_le_reverse', inv_def,
          eq_symm_apply, form_perm_apply_nth_le _ h],
    { congr,
      rcases k with _|_|k,
      { simp },
      { simp [nat.mod_eq_of_lt] },
      { have hk' : k < xs.length,
          { simpa [nat.succ_lt_succ_iff] using hk },
        suffices : xs.length.succ + 1 - (xs.length - k) = k.succ.succ,
          { simpa [←nat.sub_add_comm (nat.succ_le_of_lt hk'), nat.mod_eq_of_lt,
                   ←nat.sub_add_comm ((nat.sub_le_self _ _).trans (nat.lt_succ_self _).le),
                   nat.sub_lt_self nat.succ_pos' (nat.sub_pos_of_lt hk'),
                   (nat.sub_lt_succ xs.length k).trans (nat.lt_succ_self _), ←add_assoc] },
        rw nat.sub_sub_assoc ((nat.lt_succ_self xs.length).trans_le (nat.le_add_right _ _)).le
          hk'.le,
        simp [add_comm, nat.succ_sub] } },
    { simpa using nat.sub_lt_succ _ _ },
    { rw nth_le_reverse',
      { congr,
        rcases k with _|_|k,
        { simp },
        { simp },
        { simp only [nat.succ_sub_succ_eq_sub, length, nat.succ_add_sub_one],
          rw nat.sub_sub_assoc (nat.le_add_right _ _),
          { simp [add_comm] },
          { refine nat.succ_le_of_lt _,
            simpa [nat.succ_lt_succ_iff] using hk } } },
      { simpa using nat.sub_lt_succ _ _ } },
    { simpa [←add_assoc] using nat.sub_lt_succ _ _ },
    { exact (reverse_perm _).nodup_iff.mpr h } },
  { rw [form_perm_not_mem_apply, inv_def, eq_symm_apply, form_perm_not_mem_apply _ _ hx],
    simpa using hx }
end

lemma form_perm_pow_apply_nth_le (l : list α) (h : nodup l) (n k : ℕ) (hk : k < l.length) :
  (form_perm l ^ n) (l.nth_le k hk) = l.nth_le ((k + n) % l.length)
    (nat.mod_lt _ (k.zero_le.trans_lt hk)) :=
begin
  induction n with n hn,
  { simp [nat.mod_eq_of_lt hk] },
  { simp [pow_succ, mul_apply, hn, form_perm_apply_nth_le _ h, nat.succ_eq_add_one,
          ←nat.add_assoc] }
end

lemma form_perm_ext_iff {x y x' y' : α} {l l' : list α}
  (hd : nodup (x :: y :: l)) (hd' : nodup (x' :: y' :: l')) :
  form_perm (x :: y :: l) = form_perm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') :=
begin
  refine ⟨λ h, _, λ hr, form_perm_eq_of_is_rotated hd hr⟩,
  rw equiv.perm.ext_iff at h,
  have hx : x' ∈ (x :: y :: l),
    { have : x' ∈ {z | form_perm (x :: y :: l) z ≠ z},
        { rw [set.mem_set_of_eq, h x', form_perm_apply_head],
          simp only [mem_cons_iff, nodup_cons] at hd',
          push_neg at hd',
          exact hd'.left.left.symm },
      simpa using support_form_perm_le' _ this },
  obtain ⟨n, hn, hx'⟩ := nth_le_of_mem hx,
  have hl : (x :: y :: l).length = (x' :: y' :: l').length,
    { rw [←erase_dup_eq_self.mpr hd, ←erase_dup_eq_self.mpr hd',
          ←card_to_finset, ←card_to_finset],
      refine congr_arg finset.card _,
      rw [←finset.coe_inj, ←support_form_perm_of_nodup' _ hd (by simp),
          ←support_form_perm_of_nodup' _ hd' (by simp)],
      simp [h] },
  use n,
  apply list.ext_le,
  { rw [length_rotate, hl] },
  { intros k hk hk',
    rw nth_le_rotate,
    induction k with k IH,
    { simp_rw [nat.zero_add, nat.mod_eq_of_lt hn],
      simpa },
    { have : k.succ = (k + 1) % (x' :: y' :: l').length,
        { rw [←nat.succ_eq_add_one, nat.mod_eq_of_lt hk'] },
      simp_rw this,
      rw [←form_perm_apply_nth_le _ hd' k (k.lt_succ_self.trans hk'),
          ←IH (k.lt_succ_self.trans hk), ←h, form_perm_apply_nth_le _ hd],
      congr' 1,
      have h1 : 1 = 1 % (x' :: y' :: l').length := by simp,
      rw [hl, nat.mod_eq_of_lt hk', h1, ←nat.add_mod, nat.succ_add] } }
end

theorem nodup.nth_le_inj_iff {l : list α} (h : nodup l)
  {i j : ℕ} (hi : i < l.length) (hj : j < l.length) :
  l.nth_le i hi = l.nth_le j hj ↔ i = j :=
⟨nodup_iff_nth_le_inj.mp h _ _ _ _, by simp {contextual := tt}⟩

lemma form_perm_apply_mem_eq_self_iff (hl : nodup l) (x : α) (hx : x ∈ l) :
  form_perm l x = x ↔ length l ≤ 1 :=
begin
  obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
  rw [form_perm_apply_nth_le _ hl, hl.nth_le_inj_iff],
  cases hn : l.length,
  { exact absurd k.zero_le (hk.trans_le hn.le).not_le },
  { rw hn at hk,
    cases (nat.le_of_lt_succ hk).eq_or_lt with hk' hk',
    { simp [←hk', nat.succ_le_succ_iff, eq_comm] },
    { simpa [nat.mod_eq_of_lt (nat.succ_lt_succ hk'), nat.succ_lt_succ_iff]
      using k.zero_le.trans_lt hk' } }
end

lemma form_perm_apply_mem_ne_self_iff (hl : nodup l) (x : α) (hx : x ∈ l) :
  form_perm l x ≠ x ↔ 2 ≤ l.length :=
begin
  rw [ne.def, form_perm_apply_mem_eq_self_iff _ hl x hx, not_le],
  exact ⟨nat.succ_le_of_lt, nat.lt_of_succ_le⟩
end

lemma form_perm_concat_concat_concat (x y z : α) (xs : list α) (h : (xs ++ [x, y, z]).nodup) :
  form_perm (xs ++ [x, y, z]) = form_perm (xs ++ [x, z]) * swap y x :=
begin
  rw ←inv_inj,
  rw ←form_perm_reverse _ h,
  rw mul_inv_rev,
  rw ←form_perm_reverse,
  { simp [form_perm_cons_cons_cons] },
  { refine nodup_of_sublist _ h,
    rw append_sublist_append_left,
    refine sublist.cons2 [z] [y, z] x _,
    exact sublist_cons y [z] }
end

lemma form_perm_apply_not_mem (l : list α) (x : α) (h : x ∉ l) :
  form_perm l x = x :=
begin
  contrapose! h,
  exact form_perm_ne_self_imp_mem _ _ h
end

lemma form_perm_eq_one_iff (hl : nodup l) :
  form_perm l = 1 ↔ l.length ≤ 1 :=
begin
  cases l with hd tl,
  { simp },
  { rw ←form_perm_apply_mem_eq_self_iff _ hl hd (mem_cons_self _ _),
    split,
    { simp {contextual := tt} },
    { intro h,
      simp only [(hd :: tl).form_perm_apply_mem_eq_self_iff hl hd (mem_cons_self hd tl),
                 add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero] at h,
      simp [h] } }
end

lemma form_perm_eq_form_perm_iff {l l' : list α} (hl : l.nodup) (hl' : l'.nodup) :
  l.form_perm = l'.form_perm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 :=
begin
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩),
  { suffices : l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1,
    { simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero] },
    refine ⟨λ h, or.inr h, _⟩,
    rintro (rfl | h),
    { simp },
    { exact h } },
  { suffices : l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1,
    { simpa [eq_comm, form_perm_eq_one_iff, hl, hl', length_eq_zero, le_rfl] },
    refine ⟨λ h, or.inr h, _⟩,
    rintro (h | h),
    { simp [←h.perm.length_eq] },
    { exact h } },
  { rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩),
    { simp [form_perm_eq_one_iff, hl] },
    { suffices : ¬ (x :: y :: l) ~r [x'],
      { simpa [form_perm_eq_one_iff, hl] },
      intro h,
      simpa using h.perm.length_eq },
    { simp [form_perm_ext_iff hl hl'] } }
end

lemma sublist.mem_of_mem {α : Type*} {l l' : list α} (h : l <+ l') (x : α) (hx : x ∈ l) :
  x ∈ l' :=
h.subset hx

lemma mem_of_mem_tail {α : Type*} {l : list α} (x : α) (h : x ∈ l.tail) : x ∈ l :=
(tail_sublist _).mem_of_mem x h

lemma take_while_prefix {α : Type*} (l : list α) (p : α → Prop) [decidable_pred p] :
  l.take_while p <+: l :=
begin
  nth_rewrite_rhs 0 [←take_while_append_drop p l],
  exact (take_while p l).prefix_append (drop_while p l)
end

lemma mem_of_mem_take_while {α : Type*} (l : list α) (p : α → Prop) [decidable_pred p] (x : α)
  (h : x ∈ l.take_while p) : x ∈ l :=
(sublist_of_prefix (take_while_prefix _ _)).mem_of_mem _ h

lemma mem_of_take_while_imp {α : Type*} (l : list α) (p : α → Prop) [decidable_pred p] (x : α)
  (h : x ∈ l.take_while p) : p x :=
begin
  induction l with hd tl hl,
  { simpa [take_while] using h },
  { simp only [take_while] at h,
    split_ifs at h with hp hp,
    { rcases h with rfl|h,
      { exact hp },
      { exact hl h } },
    { simpa using h } }
end

lemma take_while_eq_self_iff {α : Type*} {l : list α} {p : α → Prop} [decidable_pred p] :
  l.take_while p = l ↔ ∀ (x ∈ l), p x :=
begin
  induction l with hd tl hl,
  { simp [take_while] },
  { simp only [take_while, mem_cons_iff, forall_eq_or_imp],
    split_ifs with h h;
    simp [hl, h] }
end

lemma is_prefix.take_while {α : Type*} {l l' : list α} (h : l <+: l')
  (p : α → Prop) [decidable_pred p] : l.take_while p <+: l'.take_while p :=
begin
  induction l with hd tl hl generalizing l',
  { simpa [take_while] using nil_prefix _ },
  { cases l' with hd' tl',
    { simpa using h },
    { rw [cons_prefix_iff] at h,
      rcases h with ⟨rfl, h⟩,
      by_cases hp : p hd,
      { simpa [take_while, hp, cons_prefix_iff] using hl h },
      { simp [take_while, hp] } } }
end

lemma is_prefix.antisymm {α : Type*} {l l' : list α} (h : l <+: l') (h' : l' <+: l) : l = l' :=
begin
  induction l with hd tl hl generalizing l',
  { simpa [eq_comm] using h' },
  { cases l' with hd' tl',
    { simpa using h },
    { rw [cons_prefix_iff] at h h',
      simpa [h.left] using hl h.right h'.right } }
end

def nodup_prefix : list α → list α
| []         := []
| (hd :: tl) := hd :: (take_while (≠ hd) (nodup_prefix tl))

@[simp] lemma nodup_prefix_nil : nodup_prefix (@nil α) = [] := rfl

@[simp] lemma nodup_prefix_cons (hd : α) (tl : list α) : nodup_prefix (hd :: tl) =
  hd :: (take_while (≠ hd) (nodup_prefix tl)) := rfl

@[simp] lemma nodup_prefix_eq_nil_iff {l : list α} :
  nodup_prefix l = [] ↔ l = [] :=
by { cases l; simp }

lemma prefix_nodup_prefix (l : list α) : nodup_prefix l <+: l :=
begin
  induction l with hd tl hl,
  { simp },
  { simpa [cons_prefix_iff] using (take_while_prefix _ _).trans hl }
end

lemma nodup_nodup_prefix (l : list α) : nodup (nodup_prefix l) :=
begin
  induction l with hd tl hl,
  { simp },
  { simp,
    split,
    { intro H,
      simpa using mem_of_take_while_imp _ _ _ H },
    { refine nodup_of_sublist _ hl,
      exact sublist_of_prefix (take_while_prefix _ _) } }
end

lemma nodup_prefix_maximal (l l' : list α) (h : l' <+: l) (hl : nodup l') :
  l' <+: nodup_prefix l :=
begin
  induction l with hd tl IH generalizing l',
  { simp only [eq_nil_iff_prefix_nil] at h,
    simp [h] },
  { cases l' with hd' tl',
    { simpa using nil.prefix_append _ },
    { rw nodup_prefix_cons,
      rw cons_prefix_iff at h ⊢,
      refine h.imp id (λ h', _),
      convert (IH _ h' (nodup_of_nodup_cons hl)).take_while (≠ hd),
      rw [eq_comm, take_while_eq_self_iff],
      rintro x hx rfl,
      simpa [h.left, hx] using hl } }
end

lemma nodup_prefix_eq_self_iff_nodup : nodup_prefix l = l ↔ nodup l :=
begin
  refine ⟨λ h, h ▸ nodup_nodup_prefix l, λ h, _⟩,
  have : l <+: nodup_prefix l := nodup_prefix_maximal _ _ (prefix_refl _) h,
  exact (this.antisymm (prefix_nodup_prefix _)).symm
end

lemma form_perm_gpow_apply_mem_imp_mem (l : list α) (x : α) (hx : x ∈ l) (n : ℤ) :
  ((form_perm l) ^ n) x ∈ l :=
begin
  by_cases h : (l.form_perm ^ n) x = x,
  { simpa [h] using hx },
  { have : x ∈ {x | (l.form_perm ^ n) x ≠ x} := h,
    rw ←set_support_apply_mem at this,
    replace this := set_support_gpow_subset _ _ this,
    simpa using support_form_perm_le' _ this }
end

lemma form_perm_pow_length_eq_one_of_nodup (hl : nodup l) :
  (form_perm l) ^ (length l) = 1 :=
begin
  ext x,
  by_cases hx : x ∈ l,
  { obtain ⟨k, hk, rfl⟩ := nth_le_of_mem hx,
    simp [form_perm_pow_apply_nth_le _ hl, nat.mod_eq_of_lt hk] },
  { have : x ∉ {x | (l.form_perm ^ l.length) x ≠ x},
    { intros H,
      refine hx _,
      replace H := set_support_gpow_subset l.form_perm l.length H,
      simpa using support_form_perm_le' _ H },
    simpa }
end

lemma sizeof_drop_lt {α : Type*} [has_sizeof α] (l : list α) (hl : 0 < l.length) (n : ℕ) (hn : 0 < n) :
  sizeof (drop n l) < sizeof l :=
begin
  induction n with n IH generalizing l,
  { simpa using hn },
  { cases l with hd tl,
    { simpa using hl },
    { dsimp only [drop],
      cases n.zero_le.eq_or_lt with hn' hn',
      { simp only [←hn', drop],
        unfold_wf,
        exact (zero_lt_one).trans_le (nat.le_add_right _ _) },
      cases tl.length.zero_le.eq_or_lt with ht ht,
      { simp only [eq_nil_of_length_eq_zero ht.symm, drop_eq_nil_of_le, length, zero_le],
        unfold_wf,
        exact (zero_lt_one).trans_le (nat.le_add_right _ _) },
      refine lt_trans (IH hn' _ ht) _,
      unfold_wf,
      exact (zero_lt_one).trans_le (nat.le_add_right _ _) } }
end

/--
Split a list into its consecutive nodup sublists.
-/
def partition_nodup : list α → list (list α)
| []          := []
| l@(x :: xs) :=
    have (drop l.nodup_prefix.length l).sizeof < l.sizeof,
      begin
        refine sizeof_drop_lt _ _ _ _;
        simp [nodup_prefix_cons],
      end,
    nodup_prefix l :: partition_nodup (drop (nodup_prefix l).length l)
end form_perm

end list
