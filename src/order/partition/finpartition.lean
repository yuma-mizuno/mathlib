/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.finset.lattice
import data.finset.pairwise
import order.atoms

/-!
# Finite partitions

In this file, we define finite partitions. A finpartition of `a : α` is a finite set of pairwise
disjoint parts `parts : finset α` which does not contain `⊥` and whose supremum is `a`.

## Constructions

We provide many ways to build finpartitions:
* `finpartition.of_erase`: Builds a finpartition by erasing `⊥` for you.
* `finpartition.of_subset`: Builds a finpartition from a subset of the parts of a previous
  finpartition.
* `finpartition.empty`: The empty finpartition of `⊥`.
* `finpartition.indiscrete`: The indiscrete, aka trivial, aka pure, finpartition made of a single
  part.
* `finpartition.discrete`: The discrete finpartition of `s : finset α` made of singletons.
* `finpartition.bind`: Puts together the finpartitions of the parts of a finpartition into a new
  finpartition.
* `finpartition.atomise`: Makes a finpartition of `s : finset α` by breaking `s` along all finsets
  in `F : finset (finset α)`. Two elements of `s` belong to the same part iff they belong to the
  same elements of `F`.

`finpartition.indiscrete` and `finpartition.bind` together form the monadic structure of
`finpartition`.

## TODO

`distrib_lattice_bot` shuld be replaced everywhere by `lattice_bot`, which we don't have.

Link `finpartition` and `setoid.is_partition`.
-/

open finset function
open_locale big_operators

variables {α β ι ι' : Type*}

lemma function.embedding.ne_apply_iff (f : α ↪ β) {a b : α} : f a ≠ f b ↔ a ≠ b :=
by rw [ne.def, f.apply_eq_iff_eq]

alias function.embedding.ne_apply_iff ↔ _ function.embedding.ne_apply

@[simp] lemma finset.erase_singleton [decidable_eq α] (a : α) : ({a} : finset α).erase a = ∅ :=
begin
  ext x,
  rw [mem_erase, mem_singleton, not_and_self],
  refl,
end

@[simp] lemma finset.map_erase [decidable_eq α] [decidable_eq β] (f : α ↪ β) (s : finset α)
  (a : α) :
  (s.erase a).map f = (s.image f).erase (f a) :=
begin
  ext b,
  simp only [mem_image, exists_prop, mem_erase, mem_map],
  split,
  { rintro ⟨a', ⟨haa', ha'⟩, rfl⟩,
    exact ⟨f.ne_apply haa', a', ha', rfl⟩ },
  { rintro ⟨h, a', ha', rfl⟩,
    exact ⟨a', ⟨ne_of_apply_ne _ h, ha'⟩, rfl⟩ }
end

@[simp] lemma finset.image_erase [decidable_eq α] [decidable_eq β] {f : α → β} (hf : injective f)
  (s : finset α) (a : α) :
  (s.erase a).image f = (s.image f).erase (f a) :=
begin
  convert finset.map_erase ⟨f, hf⟩ s a,
  rw map_eq_image,
  refl,
end

lemma disjoint.elim_finset [decidable_eq α] {s t : finset α} (h : disjoint s t) {a : α}
  (has : a ∈ s) :
  a ∉ t :=
begin
  sorry
end

lemma disjoint_sup_right' [distrib_lattice_bot α] [decidable_eq ι] {a : α} {s : finset ι}
  {f : ι → α} :
  disjoint a (s.sup f) ↔ ∀ i ∈ s, disjoint a (f i) :=
begin
  refine ⟨λ h i hi, h.mono_right (le_sup hi), λ h, _⟩,
  induction s using finset.induction with i s _ ih,
  { exact disjoint_bot_right },
  { rw sup_insert,
    exact disjoint.sup_right (h _ $ mem_insert_self _ _) (ih $ λ j hj, h _ (mem_insert_of_mem hj)) }
end

namespace finset
variables [distrib_lattice_bot α] [decidable_eq ι] [decidable_eq ι']

def sup_indep (s : finset ι) (f : ι → α) : Prop :=
∀ ⦃a⦄, a ∈ s → disjoint (f a) ((s.erase a).sup f)

variables {s t : finset ι} {f : ι → α}

lemma sup_indep.subset (ht : t.sup_indep f) (h : s ⊆ t) :
  s.sup_indep f :=
λ a ha, (ht $ h ha).mono_right $ sup_mono $ erase_subset_erase _ h

lemma sup_indep_empty (f : ι → α) : (∅ : finset ι).sup_indep f := λ a ha, ha.elim

lemma sup_indep_singleton (i : ι) (f : ι → α) : ({i} : finset ι).sup_indep f :=
λ j hj, by { rw [mem_singleton.1 hj, erase_singleton, sup_empty], exact disjoint_bot_right }

lemma sup_indep.attach (hs : s.sup_indep f) : s.attach.sup_indep (f ∘ subtype.val) :=
λ i _,
  by { rw [←finset.sup_image, image_erase subtype.val_injective, attach_image_val], exact hs i.2 }

-- This really is a `set.pairwise_disjoint` lemma, but we can't state it that way
/-- Bind operation for `sup_indep`. -/
lemma sup_indep.sup {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.sup g).sup_indep f :=
begin
  rintro i hi,
  rw disjoint_sup_right',
  refine λ j hj, _,
  rw mem_sup at hi,
  obtain ⟨i', hi', hi⟩ := hi,
  rw [mem_erase, mem_sup] at hj,
  obtain ⟨hij, j', hj', hj⟩ := hj,
  obtain hij' | hij' := eq_or_ne j' i',
  { exact disjoint_sup_right'.1 (hg i' hi' hi) _ (mem_erase.2 ⟨hij, hij'.subst hj⟩) },
  { exact (hs hi').mono (le_sup hi) ((le_sup hj).trans $ le_sup $ mem_erase.2 ⟨hij', hj'⟩) }
end

/-- Bind operation for `sup_indep`. -/
lemma sup_indep.bUnion {s : finset ι'} {g : ι' → finset ι} {f : ι → α}
  (hs : s.sup_indep (λ i, (g i).sup f)) (hg : ∀ i' ∈ s, (g i').sup_indep f) :
  (s.bUnion g).sup_indep f :=
by { rw ←sup_eq_bUnion, exact hs.sup hg }

-- Could be generalized if `set.pairwise_disjoint` were about indexed sets
lemma sup_indep.pairwise_disjoint {s : finset α} [decidable_eq α] (hs : s.sup_indep id) :
  (s : set α).pairwise_disjoint :=
λ a ha b hb hab, (hs ha).mono_right $ le_sup $ mem_erase.2 ⟨hab.symm, hb⟩

-- Could be generalized if `set.pairwise_disjoint` were about indexed sets
-- Once `finset.sup_indep` will have been generalized to non distributive lattices, we can state
-- this lemma for nondistributive atomic lattices. This setting makes the `←` implication much
-- harder.
lemma sup_inded_iff_pairwise_disjoint {s : finset α} [decidable_eq α] :
  s.sup_indep id ↔ (s : set α).pairwise_disjoint :=
begin
  refine ⟨sup_indep.pairwise_disjoint, λ hs a ha, _⟩,
  rw disjoint_sup_right',
  exact λ b hb, hs a ha b (mem_of_mem_erase hb) (ne_of_mem_erase hb).symm,
end


end finset

open finset lattice

/-- A finite partition of `a : α` is a pairwise disjoint finite set of elements whose supremum is
`a`. We forbid `⊥` as a part. -/
@[ext] structure finpartition {α : Type*} [distrib_lattice_bot α] [decidable_eq α] (a : α) :=
(parts : finset α)
(disjoint : parts.sup_indep id)
(sup_parts : parts.sup id = a)
(not_bot_mem : ⊥ ∉ parts)

attribute [protected] finpartition.disjoint

namespace finpartition
section distrib_lattice_bot
variables [distrib_lattice_bot α] [decidable_eq α]

/-- A `finpartition` constructor which does not insist on `⊥` not being a part. -/
@[simps] def of_erase [decidable_eq α] {a : α} (parts : finset α)
  (disjoint : parts.sup_indep id) (sup_parts : parts.sup id = a) :
  finpartition a :=
{ parts := parts.erase ⊥,
  disjoint := disjoint.subset (erase_subset _ _),
  sup_parts := (sup_erase_bot _).trans sup_parts,
  not_bot_mem := not_mem_erase _ _ }

/-- A `finpartition` constructor from a bigger existing finpartition. -/
@[simps] def of_subset {a b : α} (P : finpartition a) {parts : finset α}
  (subset : parts ⊆ P.parts) (sup_parts : parts.sup id = b) :
  finpartition b :=
{ parts := parts,
  disjoint := P.disjoint.subset subset,
  sup_parts := sup_parts,
  not_bot_mem := λ h, P.not_bot_mem (subset h) }

variables (α)

/-- The empty finpartition. -/
@[simps] protected def empty : finpartition (⊥ : α) :=
{ parts := ∅,
  disjoint := sup_indep_empty id,
  sup_parts := finset.sup_empty,
  not_bot_mem := not_mem_empty ⊥ }

variables {α} {a : α}

/-- The finpartition in one part, aka indiscrete finpartition. -/
@[simps] def indiscrete (ha : a ≠ ⊥) : finpartition a :=
{ parts := {a},
  disjoint := sup_indep_singleton a id,
  sup_parts := finset.sup_singleton,
  not_bot_mem := λ h, ha (mem_singleton.1 h).symm }

instance : inhabited (finpartition (⊥ : α)) := ⟨finpartition.empty α ⟩

variables (P : finpartition a)

protected lemma le {b : α} (hb : b ∈ P.parts) : b ≤ a := (le_sup hb).trans P.sup_parts.le

lemma ne_bot {b : α} (hb : b ∈ P.parts) : b ≠ ⊥ := λ h, P.not_bot_mem $ h.subst hb

lemma eq_empty (P : finpartition (⊥ : α)) : P = finpartition.empty α :=
begin
  ext a,
  exact iff_of_false (λ h, P.ne_bot h $ le_bot_iff.1 $ P.le h) (not_mem_empty a),
end

instance : unique (finpartition (⊥ : α)) := { uniq := eq_empty ..finpartition.inhabited }

variables {P}

lemma parts_eq_empty_iff : P.parts = ∅ ↔ a = ⊥ :=
begin
  simp_rw ←P.sup_parts,
  refine ⟨λ h, _, λ h, eq_empty_iff_forall_not_mem.2 (λ b hb, P.not_bot_mem _)⟩,
  { rw h,
    exact finset.sup_empty },
  { rwa ←le_bot_iff.1 ((le_sup hb).trans h.le) }
end

lemma parts_nonempty_iff : P.parts.nonempty ↔ a ≠ ⊥ :=
by rw [nonempty_iff_ne_empty, not_iff_not, parts_eq_empty_iff]

section bind

/-- Given a finpartition `P` of `a` and finpartitions of each part of `P`, this yields the
finpartition of `a` obtained by juxtaposing all the subpartitions. -/
@[simps] def bind (P : finpartition a) (Q : Π i ∈ P.parts, finpartition i) : finpartition a :=
{ parts := P.parts.attach.bUnion (λ i, (Q i.1 i.2).parts),
  disjoint := begin
    refine sup_indep.bUnion _ (λ i _, (Q i.1 i.2).disjoint),
    simp_rw finpartition.sup_parts,
    exact P.disjoint.attach,
  end,
  sup_parts := begin
    simp_rw [sup_bUnion, ←P.sup_parts],
    rw [eq_comm, ←finset.sup_attach],
    exact sup_congr rfl (λ b hb, (Q b.1 b.2).sup_parts.symm),
  end,
  not_bot_mem := λ h, begin
    rw finset.mem_bUnion at h,
    obtain ⟨⟨A, hA⟩, -, h⟩ := h,
    exact (Q A hA).not_bot_mem h,
  end }

lemma mem_bind {P : finpartition a} {Q : Π i ∈ P.parts, finpartition i} {b : α} :
  b ∈ (P.bind Q).parts ↔ ∃ A hA, b ∈ (Q A hA).parts :=
begin
  rw [bind, mem_bUnion],
  split,
  { rintro ⟨⟨A, hA⟩, -, h⟩,
    exact ⟨A, hA, h⟩ },
  { rintro ⟨A, hA, h⟩,
    exact ⟨⟨A, hA⟩, mem_attach _ ⟨A, hA⟩, h⟩ }
end

lemma card_bind (Q : Π i ∈ P.parts, finpartition i) :
  (P.bind Q).parts.card = ∑ A in P.parts.attach, (Q _ A.2).parts.card :=
begin
  apply card_bUnion,
  rintro ⟨b, hb⟩ - ⟨c, hc⟩ - hbc d,
  rw [inf_eq_inter, mem_inter],
  rintro ⟨hdb, hdc⟩,
  rw [ne.def, subtype.mk_eq_mk] at hbc,
  exact (Q b hb).ne_bot hdb (eq_bot_iff.2 $
    (le_inf ((Q b hb).le hdb) $ (Q c hc).le hdc).trans $ P.disjoint _ hb _ hc hbc),
end

end bind

/-- Adds `b` to a finpartition of `a` to make a finpartition of `a ⊔ b`. -/
@[simps] def extend [decidable_eq α] (P : finpartition a) {b c : α} (hb : b ≠ ⊥)
  (hab : disjoint a b) (hc : a ⊔ b = c) :
  finpartition c :=
{ parts := insert b P.parts,
  disjoint :=
  begin
    rw coe_insert,
    exact P.disjoint.insert (λ d hd hbd, hab.symm.mono_right $ P.le hd),
  end,
  sup_parts := by rwa [sup_insert, P.sup_parts, sup_comm],
  not_bot_mem := λ h, (mem_insert.1 h).elim hb.symm P.not_bot_mem }

lemma card_extend [decidable_eq α] (P : finpartition a) (b c : α) {hb : b ≠ ⊥} {hab : disjoint a b}
  {hc : a ⊔ b = c} :
  (P.extend hb hab hc).parts.card = P.parts.card + 1 :=
card_insert_of_not_mem $ λ h, hb $ hab.symm.eq_bot_of_le $ P.le h

end distrib_lattice_bot

section generalized_boolean_algebra
variables [generalized_boolean_algebra α] [decidable_eq α] {a : α} (P : finpartition a)

/-- Restricts a finpartition to avoid a given element. -/
def avoid (b : α) : finpartition (a \ b) :=
of_erase
  (P.parts.image (\ b))
  (P.disjoint.image_finset $ λ a, sdiff_le)
  (begin
    rw [sup_image, comp.left_id, finset.sup_sdiff_right],
    congr,
    exact P.sup_parts,
  end)

end generalized_boolean_algebra
end finpartition

/-! ### Finite partitions of finsets -/

namespace finpartition
variables [decidable_eq α] {s : finset α} (P : finpartition s)

lemma nonempty_of_mem_parts {a : finset α} (ha : a ∈ P.parts) : a.nonempty :=
nonempty_iff_ne_empty.2 $ P.ne_bot ha

lemma exists_mem {a : α} (ha : a ∈ s) : ∃ t ∈ P.parts, a ∈ t :=
by { simp_rw ←P.sup_parts at ha, exact mem_sup.1 ha }

lemma bUnion_parts : P.parts.bUnion id = s := (sup_eq_bUnion _ _).symm.trans P.sup_parts

lemma sum_card_parts : ∑ i in P.parts, i.card = s.card :=
begin
  rw ←card_bUnion P.disjoint,
  exact congr_arg finset.card P.bUnion_parts,
end

lemma parts_nonempty [nonempty α] [fintype α] (P : finpartition (univ : finset α)) :
  P.parts.nonempty :=
parts_nonempty_iff.2 univ_nonempty.ne_empty

/-- The partition in singletons. -/
@[simps] def discrete (s : finset α) : finpartition s :=
{ parts := s.map ⟨singleton, singleton_injective⟩,
  disjoint :=
    begin
      rw finset.coe_map,
      exact finset.pairwise_disjoint_range_singleton.subset (set.image_subset_range _ _),
    end,
  sup_parts := by rw [sup_map, comp.left_id, embedding.coe_fn_mk, finset.sup_singleton'],
  not_bot_mem := by simp }

lemma card_discrete : (discrete s).parts.card = s.card := finset.card_map _

section atomise

/-- Cuts `s` along the finsets in `F`: Two elements of `s` will be in the same part if they are
in the same finsets of `F`. -/
def atomise (s : finset α) (F : finset (finset α)) : finpartition s :=
of_erase
  (F.powerset.image $ λ Q, s.filter (λ i, ∀ t ∈ F, t ∈ Q ↔ i ∈ t))
  (λ x hx y hy h z hz, h begin
    rw [mem_coe, mem_image] at hx hy,
    obtain ⟨Q, hQ, rfl⟩ := hx,
    obtain ⟨R, hR, rfl⟩ := hy,
    suffices h : Q = R,
    { subst h },
    rw [inf_eq_inter, mem_inter, mem_filter, mem_filter] at hz,
    rw mem_powerset at hQ hR,
    ext i,
    refine ⟨λ hi, _, λ hi, _⟩,
    { rwa [hz.2.2 _ (hQ hi), ←hz.1.2 _ (hQ hi)] },
    { rwa [hz.1.2 _ (hR hi), ←hz.2.2 _ (hR hi)] }
  end)
  (begin
    refine (finset.sup_le $ λ t ht, _).antisymm (λ a ha, _),
    { rw mem_image at ht,
      obtain ⟨A, hA, rfl⟩ := ht,
      exact s.filter_subset _ },
    { rw [mem_sup],
      refine ⟨s.filter (λ i, ∀ t, t ∈ F → (t ∈ F.filter (λ u, a ∈ u) ↔ i ∈ t)),
        mem_image_of_mem _ (mem_powerset.2 $ filter_subset _ _), mem_filter.2 ⟨ha, λ t ht, _⟩⟩,
      rw mem_filter,
      exact and_iff_right ht }
  end)

variables {F : finset (finset α)}

lemma mem_atomise {t : finset α} :
  t ∈ (atomise s F).parts ↔ t.nonempty ∧ ∃ (Q ⊆ F), s.filter (λ i, ∀ u ∈ F, u ∈ Q ↔ i ∈ u) = t :=
by simp only [atomise, of_erase, bot_eq_empty, mem_erase, mem_image, nonempty_iff_ne_empty,
  mem_singleton, and_comm, mem_powerset, exists_prop]

lemma atomise_empty (hs : s.nonempty) : (atomise s ∅).parts = {s} :=
begin
  simp_rw [atomise, powerset_empty, image_singleton, not_mem_empty, forall_false_left,
    implies_true_iff, filter_true],
  exact erase_eq_of_not_mem (not_mem_singleton.2 hs.ne_empty.symm),
end

lemma card_atomise_le : (atomise s F).parts.card ≤ 2^F.card :=
(card_le_of_subset $ erase_subset _ _).trans $ finset.card_image_le.trans (card_powerset _).le

lemma bUnion_filter_atomise (t : finset α) (ht : t ∈ F) (hts : t ⊆ s) :
  ((atomise s F).parts.filter $ λ u, u ⊆ t).bUnion id = t :=
begin
  ext a,
  rw mem_bUnion,
  refine ⟨λ ⟨u, hu, ha⟩, (mem_filter.1 hu).2 ha, λ ha, _⟩,
  obtain ⟨u, hu, hau⟩ := (atomise s F).exists_mem (hts ha),
  refine ⟨u, mem_filter.2 ⟨hu, λ b hb, _⟩, hau⟩,
  obtain ⟨Q, hQ, rfl⟩ := (mem_atomise.1 hu).2,
  rw mem_filter at hau hb,
  rwa [←hb.2 _ ht, hau.2 _ ht]
end

end atomise
end finpartition
