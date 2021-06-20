/-
Copyright (c) 2017 Mario Carneiro All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import meta.expr
import meta.rb_map
import tactic.core

namespace tactic

/-- `copy_attribute' attr_name src tgt p d_name` copy (user) attribute `attr_name` from
   `src` to `tgt` if it is defined for `src`; unlike `copy_attribute` the primed version also copies
   the parameter of the user attribute, in the user attribute case. Make it persistent if `p` is
   `tt`; if `p` is `none`, the copied attribute is made persistent iff it is persistent on `src`  -/
meta def copy_attribute' (attr_name : name) (src : name) (tgt : name) (p : option bool := none)
  (f : expr → tactic expr := pure) : tactic unit :=
do
  (p', prio) ← has_attribute attr_name src,
  let p := p.get_or_else p',
  get_decl tgt <|> fail!"unknown declaration {tgt}",
  set_basic_attribute attr_name tgt p prio <|> (do
    user_attr_nm ← get_user_attribute_name attr_name,
    user_attr_const ← mk_const user_attr_nm,
    tac ← eval_pexpr (tactic expr)
    ``(user_attribute.get_param_untyped %%user_attr_const %%src),
    e ← tac,
    trace e,
    e'← f e,
    trace e',
    trace $ f (expr.const `prod.ok [] : expr),
    trace $ (expr.const `prod [] : expr).apply_replacement_fun (name.map_prefix $ λ n, `sum),
    tac2 ← eval_pexpr (tactic unit)
      ``(user_attribute.set %%user_attr_const %%tgt %%e' %%p %%prio),
    tac2)

private meta def transform_decl_with_prefix_fun_aux (f : name → option name) (pre tgt_pre : name)
  (attrs : list name) :
  name → command :=
λ src,
do
  let tgt := src.map_prefix (λ n, if n = pre then some tgt_pre else none),
  (get_decl tgt >> skip) <|>
  do
    decl ← get_decl src,
    (decl.type.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    (decl.value.list_names_with_prefix pre).mfold () (λ n _, transform_decl_with_prefix_fun_aux n),
    is_protected ← is_protected_decl src,
    trace decl,
    let decl := decl.update_with_fun (name.map_prefix f) tgt,
    trace decl,
    if is_protected then add_protected_decl decl else add_decl decl,
    trace $ (`(`has_mul.mul) : expr).apply_replacement_fun (name.map_prefix f) ,
    attrs.mmap' (λ n, try $ copy_attribute' n src tgt none
      (λ e : expr, return $ e.apply_replacement_fun (name.map_prefix f)))
      .

lemma  mul_inv: ℕ := 1
lemma  tat : 1*mul_inv = 1*1 := sorry
#print is_commutative
#check (`(`has_mul.mul) : expr)
set_option pp.all false
run_cmd (do
d ← get_decl `tactic.tat,
trace d.type,
let f := λ n : name, ((match n with
| `has_mul.mul := `hi
| _ := none
end) : option name),
trace "ohk",
    trace $ (expr.const `has_mul.mul [] : expr).apply_replacement_fun (name.map_prefix f) ,
trace $ d.type.apply_replacement_fun (name.map_prefix f),
trace d)
/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the function `f`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_fun (f : name → option name) (src tgt : name) (attrs : list name) :
  command :=
do transform_decl_with_prefix_fun_aux f src tgt attrs src,
   ls ← get_eqn_lemmas_for tt src,
   ls.mmap' $ transform_decl_with_prefix_fun_aux f src tgt attrs

/--
Make a new copy of a declaration,
replacing fragments of the names of identifiers in the type and the body using the dictionary `dict`.
This is used to implement `@[to_additive]`.
-/
meta def transform_decl_with_prefix_dict (dict : name_map name) (src tgt : name) (attrs : list name) :
  command :=
transform_decl_with_prefix_fun dict.find src tgt attrs

end tactic
