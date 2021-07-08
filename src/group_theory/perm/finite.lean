/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import group_theory.perm.support
import group_theory.perm.subgroup
import group_theory.perm.sign
import data.equiv.fintype

/-!

# Subgroup of finite permutations

## Main definitions

* `equiv.perm.finite`: the subgroup of `equiv.perm α` of `p : perm α` with `p.support.finite`.
* `equiv.perm.finite.sign`: the extension of `equiv.perm.sign` to finite permutations over a
not-necessarily finite type.

## Implementation details

To be able to use the existing `equiv.perm.sign` without having `[fintype α]`, we need to juggle
several subtypes of the form `↥↑p.support`. This is because `p : equiv.perm.finite α` is not
actually an `equiv.perm α` until coerced, which is necessary to use `equiv.perm.support`.
Additionally, since the finite-ness proof is via `set.finite`, all the construction of
`[fintype ↥↑p.support]` has to be done manually and noncomputably. To facilitate multiplication
of the permutations specialized to their respective supports, helped embeddings and equivalences
are defined, with helper auxiliary lemmas.

-/

open equiv set

variables {α : Type*}

section embed

variables {s t : set α} (h : s ⊆ t)
include h

/-- The subset relation implies an embedding from the subset to the superset. -/
def embed_subset : s ↪ t :=
⟨subtype.map id (λ _ hx, h hx), subtype.map_injective _ function.injective_id⟩

@[simp] lemma embed_subset_apply (x : s) : embed_subset h x = ⟨x, h x.prop⟩ := rfl

lemma range_embed_subset : range (embed_subset h) = {x | (x : α) ∈ s} :=
by { ext ⟨⟩, simp }

@[simp] lemma inv_of_mem_range_embed_subset_apply (x) [fintype s] [decidable_eq t] :
  (embed_subset h).inv_of_mem_range x = ⟨x, by simpa [range_embed_subset h] using x.prop⟩ :=
begin
  convert function.embedding.right_inv_of_inv_of_mem_range _ _,
  { simp },
  { apply_instance },
  { apply_instance }
end

end embed

namespace equiv.perm

/--
Regard a `perm α` as a permutation over the subtype of elements
that are in its support.
-/
@[simps apply]
protected def attach (p : perm α) : perm {x | p x ≠ x} :=
perm.subtype_perm p (by simp)

lemma attach_def (p : perm α) : p.attach = p.subtype_perm (by simp) := rfl

@[simp] lemma attach_one : perm.attach (1 : perm α) = 1 :=
by { ext, simp }

attribute [simps symm_apply] set_congr

@[simp] lemma inv_attach (p : perm α) : p.attach⁻¹ =
  perm_congr (set_congr (set_support_inv_eq _)) p⁻¹.attach :=
begin
  rw inv_eq_iff_mul_eq_one,
  ext,
  simp
end

lemma attach_embed_apply_mem_support (p : perm α) (t : set α)
  [fintype {x | p x ≠ x}] [decidable_eq t] (h : {x | p x ≠ x} ⊆ t) (x : t)
  (hx : (x : α) ∈ {x | p x ≠ x}) :
  p.attach.via_fintype_embedding (embed_subset h) x = ⟨p x, h (set_support_apply_mem.mpr hx)⟩ :=
begin
  rw via_fintype_embedding_apply_mem_range,
  swap,
  { simpa [range_embed_subset] using hx },
  simp
end

lemma attach_embed_apply_not_mem_support (p : perm α) (t : set α)
  [fintype {x | p x ≠ x}] [decidable_eq t] (h : {x | p x ≠ x} ⊆ t) (x : t)
  (hx : (x : α) ∉ {x | p x ≠ x}) :
  p.attach.via_fintype_embedding (embed_subset h) x =
    ⟨p x, by { convert x.prop, simpa using hx }⟩ :=
begin
  rw via_fintype_embedding_apply_not_mem_range,
  swap,
  { simpa [range_embed_subset] using hx },
  simpa [eq_comm, subtype.ext_iff] using hx
end

@[simp] lemma attach_embed_apply (p : perm α) (t : set α)
  [fintype {x | p x ≠ x}] [decidable_eq t] (h : {x | p x ≠ x} ⊆ t) (x : t) :
  p.attach.via_fintype_embedding (embed_subset h) x = ⟨p x,
    or.cases_on (em ((x : α) ∈ {x | p x ≠ x}))
    (λ hx, h (set_support_apply_mem.mpr hx))
      (λ hx, by { convert x.prop, simpa using hx })⟩ :=
begin
  by_cases hx : (x : α) ∈ {x | p x ≠ x},
  { exact attach_embed_apply_mem_support _ _ _ _ hx },
  { exact attach_embed_apply_not_mem_support _ _ _ _ hx }
end

lemma attach_mul_via_fintype_embedding [decidable_eq α]
  (p q : perm α)
  [fintype {x | p x ≠ x}]
  [fintype {x | q x ≠ x}]
  [fintype {x | (p * q) x ≠ x}] :
  (p * q).attach.via_fintype_embedding (embed_subset (set_support_mul_subset _ _)) =
  (p.attach.via_fintype_embedding (embed_subset (subset_union_left _ _))) *
      q.attach.via_fintype_embedding (embed_subset (subset_union_right _ _)) :=
by { ext, simp }

/--
The subgroup of `perm α` that have finite support.
-/
protected def finite (α : Type*) : subgroup (perm α) :=
{ carrier := {p : perm α | set.finite {x | p x ≠ x}},
  one_mem' := by simp,
  mul_mem' := λ p q hp hq, (hp.union hq).subset
  begin
    intro x,
    simp only [perm.coe_mul, mem_union_eq, mem_set_of_eq, function.comp_app, ne.def],
    intros hx,
    by_cases h : q x = x,
    { simpa [h] using hx },
    { exact or.inr h }
  end,
  inv_mem' :=
  begin
    intros p hp,
    simp only [perm.inv_def, symm_apply_eq, mem_set_of_eq, ne.def],
    convert hp,
    simp [eq_comm],
  end }

lemma finite_support_finite (p : equiv.perm.finite α) : {x | p x ≠ x}.finite :=
p.prop

@[simp] lemma mem_finite_iff (p : perm α) : p ∈ perm.finite α ↔ {x | ¬ p x = x}.finite := iff.rfl

@[simp] lemma finite_eq_top [fintype α] : perm.finite α = ⊤ :=
begin
  simp_rw [subgroup.eq_top_iff', mem_finite_iff],
  exact λ _, finite.of_fintype _
end

instance [fintype α] : has_coe_t (perm α) (perm.finite α) :=
⟨λ p, ⟨p, by simp⟩⟩

@[simp] lemma coe_coe [fintype α] (p : perm α) : ((p : perm.finite α) : perm α) = p := rfl

noncomputable instance fintype_finite_set_support (p : perm.finite α) :
  fintype {x | p x ≠ x} := finite.fintype p.prop

noncomputable instance fintype_finite_set_support_coe (p : perm.finite α) :
  fintype {x | (p : perm α) x ≠ x} := finite.fintype p.prop

@[simp] lemma sign_attach [decidable_eq α] [fintype α] (p : perm α) :
  sign p.attach = sign p :=
by simp [attach_def, sign_subtype_perm]

/--
The sign of a permutation, given that it is finite. Works for over
not-necessarily `[fintype α]` by requiring the finiteness assumption to
be provided by membership in `perm.finite α`.
See `equiv.perm.sign_eq_sign` for a proof that this function
is equal to `equiv.perm.sign` over `[fintype α]`.
-/
noncomputable def finite.sign [decidable_eq α] : perm.finite α →* units ℤ :=
monoid_hom.mk'
  (λ p, sign (perm.attach (p : perm α)))
  (λ p q, begin
    dsimp,
    letI : fintype {x | ((p : perm α) * (q : perm α)) x ≠ x},
    { refine finite.fintype _,
      exact set.finite.subset (p.prop.union q.prop) (set_support_mul_subset p q) },
    convert (via_fintype_embedding_sign
      ((p : perm α) * (q : perm α)).attach
      (embed_subset (set_support_mul_subset p q))).symm,
    have hp : sign (p : perm α).attach = sign (((p : perm α).attach).via_fintype_embedding
      (embed_subset (subset_union_left _ {x | q x ≠ x}))) := by simp,
    have hq : sign (q : perm α).attach = sign (((q : perm α).attach).via_fintype_embedding
      (embed_subset (subset_union_right {x | p x ≠ x} _))) := by simp,
    rw [hp, hq, ←sign_mul, attach_mul_via_fintype_embedding],
    refl
  end)

@[simp] lemma sign_eq_sign [decidable_eq α] [fintype α] (p : perm α) :
  finite.sign (p : perm.finite α) = sign p :=
begin
  rw [finite.sign, monoid_hom.mk'_apply],
  convert sign_attach _
end

end equiv.perm
