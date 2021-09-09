/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import algebra.group.to_additive

/-!
# Transport lattice to set notation

This file defines an attribute `to_set_notation` that can be used to
automatically transport theorems and definitions (but not inductive
types and structures) from lattice notation (inf, sup, bot, le...) to
set notation (inter, union, empty, subset...).

This tactic is identical to `to_additive`, except that it uses a different
dictionary of names it translates. See the documentation of `to_additive`
for more information on how the tactic works.
-/

namespace to_set_notation
open tactic exceptional

section performance_hack -- see Note [user attribute parameters]

local attribute [semireducible] reflected

local attribute [instance, priority 9000]
private meta def hacky_name_reflect : has_reflect name :=
λ n, `(id %%(expr.const n []) : name)

/-- An auxiliary attribute used to store the names of the additive versions of declarations
that have been processed by `to_set_notation`. -/
@[user_attribute]
private meta def aux_attr : user_attribute (name_map name) name :=
{ name      := `set_notation_aux,
  descr     := "Auxiliary attribute for `set_notation`. DON'T USE IT",
  cache_cfg := ⟨λ ns,
                ns.mfoldl
                  (λ dict n', do
                   let n := match n' with
                            | name.mk_string s pre := if s = "_set_notation" then pre else n'
                            | _ := n'
                            end,
                    param ← aux_attr.get_param_untyped n',
                    pure $ dict.insert n param.app_arg.const_name)
                  mk_name_map, []⟩,
  parser    := lean.parser.ident }

end performance_hack

/-- Dictionary used by `to_set_notation.guess_name` to autogenerate names. -/
meta def set_tr : list string → list string
| ("le" :: s)          := "subset" :: set_tr s
| ("ge" :: s)          := "superset" :: set_tr s
| ("lt" :: s)          := "ssubset" :: set_tr s
| ("gt" :: s)          := "ssuperset" :: set_tr s
| ("sup" :: s)         := "union" :: set_tr s
| ("inf" :: s)         := "inter" :: set_tr s
| ("Sup" :: s)         := "Union" :: set_tr s
| ("Inf" :: s)         := "Inter" :: set_tr s
| ("top" :: s)         := "univ" :: set_tr s
| ("bot" :: s)         := "empty" :: set_tr s
| ("compl" :: s)       := "scompl" :: set_tr s
| ("sdiff" :: s)       := "ssdiff" :: set_tr s
| ("preorder" :: s)    := "set_preorder" :: set_tr s
| ("partial" :: s)     := "set_partial" :: set_tr s
| ("semilattice" :: s) := "set_semilattice" :: set_tr s
| ("lattice" :: s)     := "set_lattice" :: set_tr s
| ("boolean" :: s)     := "set_boolean" :: set_tr s
| ("linear" :: s)      := "set_linear" :: set_tr s
| ("disjoint" :: s)    := "disjoint_set" :: set_tr s
| (x :: s)             := x :: set_tr s
| []                   := []

/-- Autogenerate target name for `to_set_notation`. -/
meta def guess_name : string → string :=
string.map_tokens ''' $ λ s, string.intercalate (string.singleton '_') $ set_tr (s.split_on '_')

/--

-/
@[user_attribute]
protected meta def attr : user_attribute unit to_additive.value_type :=
{ name      := `to_set_notation,
  descr     := "Transport lattice to set notation",
  parser    := to_additive.parser,
  after_set := some $ λ src prio persistent, do
    guard persistent <|> fail "`to_set_notation` can't be used as a local attribute",
    env ← get_env,
    val ← attr.get_param src,
    dict ← aux_attr.get_cache,
    tgt ← to_additive.target_name "to_set_notation" src val.tgt dict guess_name,
    aux_attr.set src tgt tt,
    let dict := dict.insert src tgt,
    if env.contains tgt
    then to_additive.proceed_fields env src tgt prio aux_attr
    else do
      transform_decl_with_prefix_dict dict src tgt
        [`reducible, `_refl_lemma, `simp, `instance, `refl, `symm, `trans, `elab_as_eliminator,
         `no_rsimp],
      mwhen (has_attribute' `simps src)
        (trace "Apply the simps attribute after the to_set_notation attribute"),
      match val.doc with
      | some doc := add_doc_string tgt doc
      | none := skip
      end }

add_tactic_doc
{ name                     := "to_set_notation",
  category                 := doc_category.attr,
  decl_names               := [`to_set_notation.attr],
  tags                     := ["transport", "environment", "lemma derivation"] }

end to_set_notation
