/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import category_theory.sites.pretopology
import category_theory.Fintype

/-!
# The category of Profinite Types
We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

## Implementation notes

A profinite type is defined to be a topological space which is
compact, Hausdorff and totally disconnected.

## TODO

0. Link to category of projective limits of finite discrete sets.
1. existence of products, limits(?), finite coproducts
2. `Profinite_to_Top` creates limits?
3. Clausen/Scholze topology on the category `Profinite`.

## Tags

profinite

-/

open category_theory

/-- The type of profinite topological spaces. -/
structure Profinite :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_t2 : t2_space to_Top]
[is_totally_disconnected : totally_disconnected_space to_Top]

namespace Profinite

instance : inhabited Profinite := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort Profinite := ⟨Type*, λ X, X.to_Top⟩
instance {X : Profinite} : compact_space X := X.is_compact
instance {X : Profinite} : t2_space X := X.is_t2
instance {X : Profinite} : totally_disconnected_space X := X.is_totally_disconnected

instance category : category Profinite := induced_category.category to_Top

@[simp]
lemma coe_to_Top {X : Profinite} : (X.to_Top : Type*) = X :=
rfl

end Profinite

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def Profinite_to_Top : Profinite ⥤ Top := induced_functor _

instance : concrete_category Profinite :=
{ forget := Profinite_to_Top ⋙ forget _ }

/-- The fully faithful embedding of `Profinite` in `CompHaus`. -/
@[simps] def Profinite_to_CompHaus : Profinite ⥤ CompHaus :=
{ obj := λ X, { to_Top := X.to_Top },
  map := λ _ _ f, f }

instance : full Profinite_to_CompHaus := { preimage := λ _ _ f, f }
instance : faithful Profinite_to_CompHaus := {}

@[simp] lemma Profinite_to_CompHaus_to_Top :
  Profinite_to_CompHaus ⋙ CompHaus_to_Top = Profinite_to_Top :=
rfl

#check discrete_topology.mk
#check discrete_topology
#check t2_space_discrete
#check discrete_topology
#check Profinite.mk
#check Top.discrete

def Fintype_to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ X,
  { to_Top := ⟨X, ⊥⟩,
    is_t2 := @t2_space_discrete _ _ ⟨rfl⟩,
    is_totally_disconnected := by letI:topological_space X := ⊥; letI:discrete_topology X := ⟨rfl⟩; apply_instance },
  map := λ X Y f, by letI:topological_space X := ⊥; letI:discrete_topology X := ⟨rfl⟩;
                  by letI:topological_space Y := ⊥; letI:discrete_topology Y := ⟨rfl⟩;
                  exact ⟨f, continuous_of_discrete_topology⟩,
  map_id' := λ X, rfl,
  map_comp' := λ X Y Z f g, rfl}

namespace Profinite

variables (α : Type*) [topological_space α]

open category_theory.limits

variable {J : Type*}


instance Pi.totally_disconnected_space {α : Type*} {β : α → Type*} [t₂ : Πa, topological_space (β a)]
   [∀a, totally_disconnected_space (β a)] : totally_disconnected_space (Π (a : α), β a) :=
begin
  constructor,
  intros t h1 h2,
  constructor,
  intros a b, ext,
  have H1 : subsingleton ((λ c : (Π (a : α), β a), c x )'' t),
    { exact (totally_disconnected_space.is_totally_disconnected_univ
          ( (λ (c : Π (a : α), β a), c x) '' t) (set.subset_univ _)
          (is_preconnected.image h2 _ (continuous.continuous_on (continuous_apply _)))) },
  cases H1,
  have H2 := H1 ⟨(a.1 x), by {simp, use a, split, simp}⟩,
  have H3 := H2 ⟨(b.1 x), by {simp, use b, split, simp}⟩,
  simp at H3, exact H3,
end

theorem subsingleton_of_image {α β : Type*} {f : α → β} (hf : function.injective f)
  (s : set α) (hs : subsingleton (f '' s)) : subsingleton s :=
begin
  apply subsingleton.intro,
  rintros ⟨a, ha⟩ ⟨b, hb⟩,
  ext,
  apply hf,
  simpa using @subsingleton.elim _ hs ⟨f a, ⟨a, ha, rfl⟩⟩ ⟨f b, ⟨b, hb, rfl⟩⟩,
end

instance subtype.totally_disconnected_space {α : Type*} {p : α → Prop} [topological_space α] [t2_space α] [totally_disconnected_space α] : totally_disconnected_space (subtype p) :=
  ⟨λ s h1 h2,
    subsingleton_of_image subtype.val_injective s (
      totally_disconnected_space.is_totally_disconnected_univ (subtype.val '' s) (set.subset_univ _)
        ( (is_preconnected.image h2 _) (continuous.continuous_on (@continuous_subtype_val _ _ p)) ) ) ⟩

theorem subset_of_inter_eq_self_left {s t : set α} (h : s ∩ t = s) : s ⊆ t :=
λ x h1, set.mem_of_mem_inter_right (by {rw h, exact h1})

theorem subset_of_inter_eq_self_right {s t : set α} (h : t ∩ s = s) : s ⊆ t :=
λ x h1, set.mem_of_mem_inter_left (by {rw h, exact h1})

lemma continuous_on.preimage_clopen_of_clopen {α β: Type*} [topological_space α] [topological_space β]
  {f : α → β} {s : set α} {t : set β} (hf : continuous_on f s) (hs : is_clopen s)
  (ht : is_clopen t) : is_clopen (s ∩ f⁻¹' t) :=
⟨continuous_on.preimage_open_of_open hf hs.1 ht.1, continuous_on.preimage_closed_of_closed hf hs.2 ht.2⟩

lemma inter_compl_nonempty_iff_left {α : Type*} {s t : set α} : (tᶜ ∩ s).nonempty ↔ ¬ s ⊆ t :=
begin
  split,
  { rintros ⟨x ,xs, xt⟩ sub,
    exact xs (sub xt) },
  { intros h,
    rcases set.not_subset.mp h with ⟨x, xs, xt⟩,
    exact ⟨x, xt, xs⟩ }
end

lemma is_clopen_Inter {α β : Type*} [topological_space α] [fintype β] {s : β → set α}
  (h : ∀ i, is_clopen (s i)) : is_clopen (⋂ i, s i) :=
⟨(is_open_Inter (forall_and_distrib.1 h).1), (is_closed_Inter (forall_and_distrib.1 h).2)⟩

lemma is_clopen_bInter {α β : Type*} {s : finset β} [topological_space α] {f : β → set α} :
  (∀i∈s, is_clopen (f i)) → is_clopen (⋂i∈s, f i) :=
begin
  intro h,
  split,
  { apply is_open_bInter ⟨finset_coe.fintype s⟩,
    rintros i hi,
    exact (h i hi).1,
  },
  { show is_closed (⋂ (i : β) (H : i ∈ (↑s : set β)), f i),
    rw set.bInter_eq_Inter,
    apply is_closed_Inter,
    rintro ⟨i, hi⟩,
    exact (h i hi).2
  }
end

theorem is_clopen_inter_of_partition_clopen {α : Type*} [topological_space α] {Z a b : set α} (h : is_clopen Z)
  (cover : Z ⊆ a ∪ b) (ha : is_open a) (hb : is_open b) (hab : a ∩ b = ∅) : is_clopen (Z ∩ a) :=
begin
  split,
    exact is_open_inter h.1 ha,
  rw ←(@subtype.range_coe _ Z),
  apply (closed_embedding.closed_iff_preimage_closed
    (is_closed.closed_embedding_subtype_coe h.2) (set.inter_subset_left _ a)).2,
  apply is_open_compl_iff.1,
  have H2 :  ((coe : Z → α) ⁻¹' (set.range (coe : Z → α) ∩ a))ᶜ = ((coe : Z → α) ⁻¹' (set.range (coe : Z → α) ∩ b)),
  {
    apply set.eq_of_subset_of_subset,
    {
      rw set.compl_subset_iff_union,
      -- TODO: avoid this shit:
      cases h, dsimp, simp, ext1, cases x, dsimp, simp, solve_by_elim,
    },
    rw [set.subset_compl_iff_disjoint],
    simp only [set.univ_inter, subtype.coe_preimage_self, subtype.range_coe_subtype, set.preimage_inter, set.set_of_mem_eq],
    rw [←set.preimage_inter, set.inter_comm],
    apply set.preimage_eq_empty,
    rw hab,
    exact set.empty_disjoint _,
  },
  rw H2,
  apply continuous.is_open_preimage continuous_subtype_coe,
  rw subtype.range_coe,
  exact is_open_inter h.1 hb,
end

theorem is_preconnected_iff_subset_of_disjoint_closed {α : Type*} {s : set α} [topological_space α] :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hs : s ⊆ u ∪ v) (huv : s ∩ (u ∩ v) = ∅),
  s ⊆ u ∨ s ⊆ v :=
begin
  split; intro h,
  { intros u v hu hv hs huv,
    rw is_preconnected_closed_iff at h,
    specialize h u v hu hv hs,
    contrapose! huv,
    rw set.ne_empty_iff_nonempty,
    simp [set.not_subset] at huv,
    rcases huv with ⟨⟨x, hxs, hxu⟩, ⟨y, hys, hyv⟩⟩,
    have hxv : x ∈ v := or_iff_not_imp_left.mp (hs hxs) hxu,
    have hyu : y ∈ u := or_iff_not_imp_right.mp (hs hys) hyv,
    exact h ⟨y, hys, hyu⟩ ⟨x, hxs, hxv⟩ },
  { rw is_preconnected_closed_iff,
    intros u v hu hv hs hsu hsv,
    rw ← set.ne_empty_iff_nonempty,
    intro H,
    specialize h u v hu hv hs H,
    contrapose H,
    apply set.ne_empty_iff_nonempty.mpr,
    cases h,
    { rcases hsv with ⟨x, hxs, hxv⟩, exact ⟨x, hxs, ⟨h hxs, hxv⟩⟩ },
    { rcases hsu with ⟨x, hxs, hxu⟩, exact ⟨x, hxs, ⟨hxu, h hxs⟩⟩ } }
end

theorem is_preconnected_iff_subset_of_fully_disjoint_closed {α : Type*} {s : set α} [topological_space α] (hs : is_closed s) :
  is_preconnected s ↔
  ∀ (u v : set α) (hu : is_closed u) (hv : is_closed v) (hss : s ⊆ u ∪ v) (huv : u ∩ v = ∅),
  s ⊆ u ∨ s ⊆ v :=
begin
  split,
  {
    intros,
    apply is_preconnected_iff_subset_of_disjoint_closed.1 ᾰ u v hu hv hss,
    rw huv,
    exact set.inter_empty s,
  },
  intro H,
  rw is_preconnected_iff_subset_of_disjoint_closed,
  intros u v hu hv hss huv,
  have H1 := H (u ∩ s) (v ∩ s),
  rw [(@set.subset_inter_iff _ u s s), (@set.subset_inter_iff _ v s s)] at H1,
  simp only [set.subset.refl, and_true] at H1,
  apply H1 (is_closed_inter hu hs) (is_closed_inter hv hs),
  {
    rw ←set.inter_distrib_right,
    apply set.subset_inter_iff.2,
    split,
      exact hss,
    exact set.subset.refl s,
  },
  {
  conv in (v ∩ s) {rw set.inter_comm},
  rw set.inter_assoc,
  conv in (s ∩ (s ∩ v)) {rw [←set.inter_assoc, set.inter_self s]},
  rw [set.inter_comm, set.inter_assoc],
  conv in (v ∩ u) {rw set.inter_comm},
  exact huv,
  }
end

theorem preconnected_subset_clopen {α : Type*} [topological_space α] {s t : set α} (h : is_clopen s) (h1 : is_preconnected t) :
  (s ∩ t).nonempty → t ⊆ s :=
begin
  intro h2,
  let v := sᶜ,
  apply subset_of_inter_eq_self_left,
  let u := (coe : (t → α)) ⁻¹' s,
  have hu : is_clopen u,
  {
    rw [←(set.inter_univ u), set.inter_comm],
    apply (continuous_on.preimage_clopen_of_clopen
          (continuous_iff_continuous_on_univ.1 continuous_subtype_coe) is_clopen_univ h),
  },
  cases (@is_clopen_iff _ _ (is_preconnected_iff_preconnected_space.1 h1) _).1 hu,
    {
      exfalso,
      apply set.nonempty.ne_empty h2,
      suffices : (coe : (t → α)) ⁻¹' (s ∩ t) = ∅,
      {
        rw [←set.preimage_eq_empty_iff, subtype.range_coe, set.disjoint_iff_inter_eq_empty] at this,
        rw [set.inter_assoc, set.inter_self t] at this,
        exact this,
      },
      rw [set.preimage_inter, subtype.coe_preimage_self, set.inter_univ],
      exact h_1,
    },
    {
      rw [←subtype.coe_preimage_self t, subtype.preimage_coe_eq_preimage_coe_iff, set.inter_self t] at h_1,
      rw set.inter_comm,
      exact h_1,
    },
end

lemma sub_refined_of_sub_partition {α : Type*} {Z a b u v : set α} (hZ : Z ⊆ u)
  (hau : a ⊆ u) (hbv : b ⊆ v) (Zab : Z ⊆ a ∪ b) (hab : a ∩ b = ∅) (huv : u ∩ v = ∅) : Z ⊆ a :=
begin
rw [←set.compl_compl u, set.subset_compl_iff_disjoint] at hZ,
have H : Z ∩ b = ∅,
{
  rw [set.inter_comm, ←set.subset_compl_iff_disjoint] at huv,
  apply set.eq_empty_of_subset_empty,
  rw ←hZ,
  exact set.inter_subset_inter (set.subset.refl Z) (set.subset.trans hbv huv),
},
rw ←set.subset_compl_iff_disjoint at H,
have H1 := set.subset_inter Zab H,
rw [set.inter_distrib_right, set.inter_compl_self, set.union_empty] at H1,
exact set.subset.trans H1 (set.inter_subset_left a bᶜ),
end

lemma connected_component_Inter {α : Type*} [topological_space α] [t2_space α] [compact_space α] :
  ∀ x : α, connected_component x = ⋂ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z :=
begin
  intro x,
  apply set.eq_of_subset_of_subset,
  { exact (set.subset_Inter (λ Z, preconnected_subset_clopen Z.2.1
    (is_connected_connected_component).2 (set.nonempty_of_mem
    (set.mem_inter Z.2.2 (mem_connected_component))))) },
  {
    have hs : @is_closed _ _inst_2 (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z),
    { exact is_closed_Inter (λ Z, Z.2.1.2) },
    apply subset_connected_component, {
      apply (is_preconnected_iff_subset_of_fully_disjoint_closed hs).2,
      intros a b ha hb hab ab_empty,
      haveI := @normal_of_compact_t2 α _ _ _,
      rcases normal_separation a b ha hb (disjoint_iff.2 ab_empty) with ⟨u, v, hu, hv, hau, hbv, huv⟩,
      suffices : ∃ (Z : set α), is_clopen Z ∧ x ∈ Z ∧ Z ⊆ u ∪ v, {
        cases this with Z H,
        rw [set.disjoint_iff_inter_eq_empty] at huv,
        have H1 := is_clopen_inter_of_partition_clopen H.1 H.2.2 hu hv huv,
        rw [set.union_comm] at H,
        rw [set.inter_comm] at huv,
        have H2 := is_clopen_inter_of_partition_clopen H.1 H.2.2 hv hu huv,
        by_cases (x ∈ u), {
          left,
          suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ u, {
            rw set.inter_comm at huv,
            exact sub_refined_of_sub_partition this hau hbv hab ab_empty huv },
          {
            apply set.subset.trans _ (set.inter_subset_right Z u),
            apply set.Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
            ⟨Z ∩ u, by {split, exact H1, apply set.mem_inter H.2.1 h}⟩ } },
        have h1 : x ∈ v,
        {
          cases (set.mem_union x u v).1 (set.mem_of_subset_of_mem (set.subset.trans hab
            (set.union_subset_union hau hbv)) (set.mem_Inter.2 (λ i, i.2.2))) with h1 h1,
          { exfalso, apply h, exact h1},
          { exact h1} },
        right,
        suffices : (⋂ (Z : {Z : set α // is_clopen Z ∧ x ∈ Z}), ↑Z) ⊆ v, {
            rw set.union_comm at hab,
            rw set.inter_comm at ab_empty,
            exact sub_refined_of_sub_partition this hbv hau hab ab_empty huv },
          {
            apply set.subset.trans _ (set.inter_subset_right Z v),
            apply set.Inter_subset (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, ↑Z)
            ⟨Z ∩ v, by {split, exact H2, apply set.mem_inter H.2.1 h1}⟩ } },
      have H1 := (is_compact.inter_Inter_nonempty (is_closed.compact (is_closed_compl_iff.2 (is_open_union hu hv)))
          (λ Z : {Z : set α // is_clopen Z ∧ x ∈ Z}, Z) _),
      rw [←not_imp_not, not_forall, set.not_nonempty_iff_eq_empty, set.inter_comm] at H1,
      have huv_union := set.subset.trans hab (set.union_subset_union hau hbv),
      rw [←set.compl_compl (u ∪ v), set.subset_compl_iff_disjoint] at huv_union,
      replace H1 := H1 huv_union,
      cases H1 with Zi H2,
      existsi (⋂ (U ∈ Zi), subtype.val U),
      split,
        { apply @is_clopen_bInter _ _ _ _ _ _, exact (λ Z hZ, Z.2.1) },
        { split,
          { exact set.mem_bInter_iff.2 (λ Z hZ, Z.2.2) },
          { rw [inter_compl_nonempty_iff_left, not_not] at H2, exact H2 } },
      exact λ Z, Z.2.1.2 },
  exact set.mem_Inter.2 (λ Z, Z.2.2) },
end

variables [small_category J]
variable G : J ⥤ Profinite

def limit_cone (F : J ⥤ Profinite) : cone F :=
{ X := { to_Top := { α := { u : Π j, F.obj j // ∀ {j j'} (f : j ⟶ j'), F.map f (u j) = u j' } },
        is_compact :=
          compact_iff_compact_space.1 (compact_of_is_closed_subset compact_univ
            ( begin
                convert (_:is_closed (⋂ (j j' : J) (f : j ⟶ j'), {u : Π j, F.obj j | F.map f (u j) = u j'})),
                  { ext1, simp only [forall_apply_eq_imp_iff', set.mem_sInter, set.mem_range, set.mem_Inter, set.mem_set_of_eq, exists_imp_distrib], refl },
                exact (
                  is_closed_Inter (λ j, is_closed_Inter (λ j', is_closed_Inter
                  (λ f, is_closed_eq ((F.map f).2.comp (continuous_apply _)) (continuous_apply _))))),
              end )
            (set.subset_univ _)),
        is_t2 := subtype.t2_space,
        is_totally_disconnected := subtype.totally_disconnected_space},
  π := { app := λ j, ⟨ λ u, u.val j,
    begin
      dsimp only [set.subset_univ, set.mem_Inter, set.mem_set_of_eq],
      convert (_:continuous ((λ u : (Π j', F.obj j'), u j) ∘ subtype.val)),
      exact (continuous.comp (continuous_apply _) continuous_subtype_val),
    end ⟩ } }

def limit_cone_is_limit (F : J ⥤ Profinite) : is_limit (limit_cone F) :=
{ lift := λ s, ⟨λ (x : s.X), ⟨λ j, s.π.app j x, λ j j' f,
        by {  rw ←Top.comp_app,
              have H1 : (s.π.app j ≫ F.map f).to_fun = (s.π.app j').to_fun, { rw cone.w s f },
              apply congr_fun H1 _,}⟩,
    continuous_subtype_mk _ (continuous_pi (λ i, (s.π.app i).2)) ⟩,
  uniq' := by {intros, ext x j, apply (congr_fun (congr_arg (@continuous_map.to_fun s.X ( F.obj j) _ _) (w j)) x), } }

instance Profinite_has_limits : has_limits Profinite :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

--lemma profinite_is_limit_of_discrete {ι : Type*} (I : ι → Type) (h : ∀ i, fintype (I i)) (X : Profinite) : _

def proetale_pretopology : pretopology Profinite :=
{ coverings := λ X, {S | (∀ x, ∃ Y (f : Y ⟶ X) y, S f ∧ f y = x) ∧
                         set.finite {Y | nonempty {f : Y ⟶ X | S f}} ∧
                         ∀ Y, set.finite {f : Y ⟶ X | S f}},
  has_isos := λ X Y f i,
  begin
    resetI,
    refine ⟨λ z, ⟨_, f, inv ((forget _).map f) z, presieve.singleton_self _, congr_fun (is_iso.inv_hom_id ((forget Profinite).map f)) z⟩, _, _⟩,
    { suffices : {Z : Profinite | nonempty {g : Z ⟶ X | presieve.singleton f g}} = {Y},
        rw this,
        apply set.finite_singleton Y,
      rw set.eq_singleton_iff_unique_mem,
      split,
      { exact ⟨⟨f, presieve.singleton_self _⟩⟩ },
      { rintro Z ⟨_, ⟨_⟩⟩,
        refl } },
    { intro Z,
      by_cases (Z = Y),
      { cases h,
        suffices : {g : Y ⟶ X | presieve.singleton f g} = {f},
          rw this,
          apply set.finite_singleton,
        rw set.eq_singleton_iff_unique_mem,
        split,
        apply presieve.singleton.mk,
        rintro f ⟨_⟩,
        refl },
      { suffices : {g : Z ⟶ X | presieve.singleton f g} = ∅,
          rw this,
          refine set.finite_empty,
        rw set.eq_empty_iff_forall_not_mem,
        rintro g ⟨_⟩,
        apply h, refl } }
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨surj, fin_dom, fin_arr⟩,
    refine ⟨_, _, _⟩,
    { intro y,
      rcases surj (f y) with ⟨Z, g, z, hg, gf⟩,
      refine ⟨_, _, _, pullback_arrows.mk _ _ hg, _⟩,
      sorry,
      sorry },
    { sorry,

    },
    sorry,
  end,
  transitive := sorry, }



/-

{ sieves := λ A, {S | ∀ x, ∃ B (f : B ⟶ A) b, S.arrows f ∧ f b = x},
  top_mem' := λ A, (λ x, by {use A, use (𝟙 A), use x, split, work_on_goal 0 { exact dec_trivial }, refl,}),
  pullback_stable' := λ X Y S f h, (λ y,
    begin
      cases h (f y),
    end),
  transitive' := _ }

def procompletion_setoid : setoid α :=
⟨ λ x y, y ∈ connected_component x,
  ⟨ λ x, mem_connected_component,
    begin
      intros x y h1,
      rw ←connected_component_eq h1,
      exact mem_connected_component,
    end,
    begin
      intros x y z h1 h2,
      rw [(connected_component_eq h1), (connected_component_eq h2)],
      exact mem_connected_component
    end
⟩⟩
local attribute [instance] procompletion_setoid

--lemma eqv_class_connected_component (s : procompletion_setoid.classes) :

#check quotient_map_iff.1
def CompHaus_to_Profinite : CompHaus ⥤ Profinite :=
{ obj := λ X,
  { to_Top := { α := quotient (procompletion_setoid X.to_Top.α)},
    is_compact := quotient.compact_space,
    is_t2 :=
    begin
      constructor, intros x y,
      apply quotient.induction_on x,
      apply quotient.induction_on y,
      intros a b ne,
      have top_thing : ∃ (u v : set X.to_Top.α), is_open u ∧ is_open v
        ∧ connected_component a ⊆ u ∧ connected_component b ⊆ v ∧ u ∩ v = ∅,
      {
        haveI := (@normal_of_compact_t2 _ _ X.is_compact X.is_hausdorff),
        simp_rw ←set.disjoint_iff_inter_eq_empty,
        apply normal_space.normal (connected_component a) (connected_component b)
          (is_closed_connected_component) is_closed_connected_component _,
        sorry,
      },
    cases top_thing with u H,
    cases H with v H,
    cases H with Ou H,
    cases H with Ov H,
    cases H with a_u H,
    cases H with b_v disj,
    use ((quotient.mk)'' u),
    use ((quotient.mk)'' v),
    split,
      {
        rw (quotient_map_iff.1 quotient_map_quot_mk).2,

      }
    {split,
      {sorry},
    {split,
      {sorry},
    {split,
     {sorry},
    sorry
    }}}
    end


    ,
    is_totally_disconnected := _ },
  map := _,
  map_id' := _,
  map_comp' := _,}

-/
end Profinite
