/-
Copyright (c) 2020 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/

import data.rat.meta_defs
import tactic.norm_num
import data.tree
import meta.expr

/-!
# A tactic for canceling numeric denominators

This file defines tactics that cancel numeric denominators from field expressions.

As an example, we want to transform a comparison `5*(a/3 + b/4) < c/3` into the equivalent
`5*(4*a + 3*b) < 4*c`.

## Implementation notes

The tooling here was originally written for `linarith`, not intended as an interactive tactic.
The interactive version has been split off because it is sometimes convenient to use on its own.
There are likely some rough edges to it.

Improving this tactic would be a good project for someone interested in learning tactic programming.
-/

def rat.lcm (a : ℚ) (b : ℚ) : ℚ
  := if a = 0 then (abs b) else if b = 0 then (abs a) else
    rat.mk ((abs a.num).to_nat.lcm b.num.to_nat) (a.denom.gcd b.denom)
def rat.gcd (a : ℚ) (b : ℚ) : ℚ
  := rat.mk ((abs a.num).to_nat.gcd b.num.to_nat) (a.denom.lcm b.denom)

namespace cancel_factors

/-! ### Lemmas used in the procedure -/

lemma mul_subst {α} [comm_ring α] {n1 n2 k c e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
     (h3 : c*n1*n2 = k) : k * (e1 * e2) = c * t1 * t2 :=
by rw [←h3, mul_assoc c, mul_assoc c, mul_comm n1, mul_assoc n2, ←mul_assoc n1, h1,
      ←mul_assoc n2, mul_comm n2, mul_assoc t1, h2, mul_assoc]

lemma div_subst {α} [field α] {n1 n2 k c e1 e2 t1 t2 : α} (h1 : n1 * e1 = t1) (h2 : n2 * e2 = t2)
     (h3 : c*n1/n2 = k) : k * (e1 / e2) = c * t1 / t2 :=
begin
  rw [←h3, mul_div_assoc, mul_assoc c, div_mul_div, h1, h2, ←mul_div_assoc],
end

lemma add_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 + e2) = t1 + t2 := by simp [left_distrib, *]

lemma sub_subst {α} [ring α] {n e1 e2 t1 t2 : α} (h1 : n * e1 = t1) (h2 : n * e2 = t2) :
      n * (e1 - e2) = t1 - t2 := by simp [left_distrib, *, sub_eq_add_neg]

lemma neg_subst {α} [ring α] {n e t : α} (h1 : n * e = t) : n * (-e) = -t := by simp *

lemma cancel_factors_lt {α} [linear_ordered_field α] {v a b a' b' : α} (ha : v*a = a')
  (hb : v*b = b') (v_pos : 0 < v) : (a < b) = (a' < b') :=
by rw [←ha, ←hb, mul_lt_mul_left v_pos]

lemma cancel_factors_le {α} [linear_ordered_field α] {v a b a' b' : α} (ha : v*a = a')
  (hb : v*b = b') (v_pos : 0 < v) : (a ≤ b) = (a' ≤ b') :=
begin
  rw [←ha, ←hb, mul_le_mul_left v_pos]
end

lemma cancel_factors_eq {α} [linear_ordered_field α] {v a b a' b' : α} (ha : v*a = a')
  (hb : v*b = b') (v_pos : 0 < v) : (a = b) = (a' = b') :=
begin
  rw [←ha, ←hb],
  exact propext (mul_right_inj' (ne_of_gt v_pos)).symm
end

open tactic expr

/-! ### Computing cancelation factors -/

open tree

/--
`find_cancel_factor e` produces a rational number `n`, such that multiplying `e` by `n` will
be able to cancel all the numeric denominators in `e`. The returned `tree` describes how to
distribute the value `n` over products inside `e`.
-/

meta def find_cancel_factor : expr → ℚ × tree ℚ
| `(%%e1 + %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, node lcm t1 t2)
| `(%%e1 - %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, lcm := v1.lcm v2 in
  (lcm, node lcm t1 t2)
| `(%%e1 * %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1*v2 in
  (pd, node pd t1 t2)
| `(%%e1 / %%e2) :=
  let (v1, t1) := find_cancel_factor e1, (v2, t2) := find_cancel_factor e2, pd := v1/v2 in
  (pd, node pd t1 t2)
| `(-%%e) := find_cancel_factor e
| e := (let q := match e.to_nonneg_rat with
  | some q := q.inv
  | none := 1
  end in (q, node q tree.nil tree.nil))

/-
`mk_prod_prf n tr e` produces a proof of `n*e = e'`, where numeric denominators have been
canceled in `e'`, distributing `n` proportionally according to `tr`.
-/
meta def mk_prod_prf : ℚ → tree ℚ → expr → tactic expr
| v (node _ lhs rhs) `(%%e1 + %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2,
     mk_app ``add_subst [v1, v2]
| v (node _ lhs rhs) `(%%e1 - %%e2) :=
  do v1 ← mk_prod_prf v lhs e1, v2 ← mk_prod_prf v rhs e2, mk_app ``sub_subst [v1, v2]
| v (node n lhs@(node ln _ _) rhs@(node rn _ _)) `(%%le * %%re) :=
  do tp ← infer_type le, lpf ← mk_prod_prf ln lhs le, rpf ← mk_prod_prf rn rhs re,
     let v0 := v / (ln * rn),
     ln' ← tp.of_rat ln, rn' ← tp.of_rat rn, v' ← tp.of_rat v, v0' ← tp.of_rat v0,
     ntp ← to_expr ``(%%v0' * %%ln' * %%rn' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     lpft ← infer_type lpf,
     rpft ← infer_type rpf,
     mk_app ``mul_subst [lpf, rpf, npf]
| v (node n lhs@(node ln _ _) rhs@(node rn _ _)) `(%%le / %%re) :=
  do tp ← infer_type le, lpf ← mk_prod_prf ln lhs le, rpf ← mk_prod_prf rn rhs re,
     let v0 := v / (ln / rn),
     ln' ← tp.of_rat ln, rn' ← tp.of_rat rn, v' ← tp.of_rat v, v0' ← tp.of_rat v0,
     ntp ← to_expr ``(%%v0' * %%ln' / %%rn' = %%v'),
     (_, npf) ← solve_aux ntp `[norm_num, done],
     mk_app ``div_subst [lpf, rpf, npf]
| v t `(-%%e) := do v' ← mk_prod_prf v t e, mk_app ``neg_subst [v']
| v _ e :=
  do tp ← infer_type e,
     v' ← tp.of_rat v,
     e' ← to_expr ``(%%v' * %%e),
     mk_app `eq.refl [e']

/--
Given `e`, a term with rational division, produces a natural number `n` and a proof of `n*e = e'`,
where `e'` has no division. Assumes "well-behaved" division.
-/
meta def derive (e : expr) : tactic (ℕ × expr) :=
do
  let (v, t) := find_cancel_factor e,
  let n := v.num.to_nat,
  prod.mk n <$> mk_prod_prf n t e <|>
  fail!"cancel_factors.derive failed to normalize {e}. Are you sure this is well-behaved division?"

/--
`find_comp_lemma e` arranges `e` in the form `lhs R rhs`, where `R ∈ {<, ≤, =}`, and returns
`lhs`, `rhs`, and the `cancel_factors` lemma corresponding to `R`.
-/
meta def find_comp_lemma : expr → option (expr × expr × name)
| `(%%a < %%b) := (a, b, ``cancel_factors_lt)
| `(%%a ≤ %%b) := (a, b, ``cancel_factors_le)
| `(%%a = %%b) := (a, b, ``cancel_factors_eq)
| `(%%a ≥ %%b) := (b, a, ``cancel_factors_le)
| `(%%a > %%b) := (b, a, ``cancel_factors_lt)
| _ := none

/--
`cancel_denominators_in_type h` assumes that `h` is of the form `lhs R rhs`,
where `R ∈ {<, ≤, =, ≥, >}`.
It produces an expression `h'` of the form `lhs' R rhs'` and a proof that `h = h'`.
Numeric denominators have been canceled in `lhs'` and `rhs'`.
-/
meta def cancel_denominators_in_type (h : expr) : tactic (expr × expr) :=
do some (lhs, rhs, lem) ← return $ find_comp_lemma h | fail "cannot kill factors",
   let (lv, ltr) := find_cancel_factor lhs,
   let (rv, rtr) := find_cancel_factor rhs,
   let v := lv.lcm rv,
   lpf ← mk_prod_prf v ltr lhs,
   rpf ← mk_prod_prf v rtr rhs,
   tp ← infer_type lhs,
   v ← tp.of_rat v,
   v_pos ← to_expr ``(0 < %%v),
   (_, v_pos) ← solve_aux v_pos `[norm_num, done],
   pf ← mk_app lem [lpf, rpf, v_pos],
   pf_tp ← infer_type pf,
   return ((find_comp_lemma pf_tp).elim (default _) (prod.fst ∘ prod.snd), pf)

end cancel_factors

/-! ### Interactive version -/

setup_tactic_parser
open tactic expr cancel_factors

/--
`cancel_denoms` attempts to remove numerals from the denominators of fractions.
It works on propositions that are field-valued inequalities.

```lean
variables {α : Type} [linear_ordered_field α] (a b c : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c :=
begin
  cancel_denoms at h,
  exact h
end

example (h : a > 0) : a / 5 > 0 :=
begin
  cancel_denoms,
  exact h
end
```
-/
meta def tactic.interactive.cancel_denoms (l : parse location) : tactic unit :=
do locs ← l.get_locals,
   tactic.replace_at cancel_denominators_in_type locs l.include_goal >>= guardb
     <|> fail "failed to cancel any denominators",
   tactic.interactive.norm_num [simp_arg_type.symm_expr ``(mul_assoc)] l

add_tactic_doc
{ name := "cancel_denoms",
  category := doc_category.tactic,
  decl_names := [`tactic.interactive.cancel_denoms],
  tags := ["simplification"] }
