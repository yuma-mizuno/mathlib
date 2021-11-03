/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Ethan Pronovost
-/
import data.list.basic
import algebra.group_power.basic

/-!
# Products / sums of lists of terms of a monoid

This file provides basic results about `list.prod` (definition in `data.list.defs`) in a monoid.
It is in a separate file so that `data.list.basic` does not depend on `algebra.group_power.basic`.
-/

open nat

namespace list

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

@[simp, priority 500, to_additive]
theorem prod_repeat [monoid α] (a : α) (n : ℕ) : (repeat a n).prod = a ^ n :=
begin
  induction n with n ih,
  { rw pow_zero, refl },
  { rw [list.repeat_succ, list.prod_cons, ih, pow_succ] }
end

@[to_additive]
lemma prod_le_of_forall_le [ordered_comm_monoid α] (l : list α) (n : α) (h : ∀ (x ∈ l), x ≤ n) :
  l.prod ≤ n ^ l.length :=
begin
  induction l with y l IH,
  { simp },
  { specialize IH (λ x hx, h x (mem_cons_of_mem _ hx)),
    have hy : y ≤ n := h y (mem_cons_self _ _),
    simpa [pow_succ] using mul_le_mul' hy IH }
end

@[simp, to_additive]
theorem prod_map_mul [comm_monoid β] {f g : α → β} :
  ∀ {l : list α}, prod (l.map $ λa, f a * g a) = prod (l.map f) * prod (l.map g)
| []         := by simp only [mul_one, map_nil, prod_nil]
| (hd :: tl) :=
begin
  simp only [map_cons, prod_cons, prod_map_mul],
  rw [mul_assoc, ←mul_assoc (g hd), mul_assoc (f hd), ←mul_assoc _ (g hd), mul_comm _ (g hd)],
end

@[to_additive]
lemma prod_map_prod_map [comm_monoid γ] {f : α → β → γ} {t : list β} :
  ∀ {s : list α}, (prod $ s.map $ λ (a : α), prod $ t.map (f a)) =
                  (prod $ t.map $ λ (b : β), prod $ s.map (λ (a : α), f a b))
| []         := by simp only [prod_repeat, one_pow, map_nil, prod_nil, map_const]
| (hd :: tl) := by simp only [map_cons, prod_cons, prod_map_mul, prod_map_prod_map]

end list
