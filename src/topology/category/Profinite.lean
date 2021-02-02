/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import category_theory.sites.pretopology
import category_theory.Fintype
import topology.subset_properties
import category_theory.adjunction.reflective


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
@[simps, derive [full, faithful]]
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

def Fintype_to_Profinite : Fintype ⥤ Profinite :=
{ obj := λ X,
  { to_Top := ⟨X, ⊥⟩,
    is_t2 := @t2_space_discrete _ _ ⟨rfl⟩,
    is_totally_disconnected := by letI:topological_space X := ⊥; letI:discrete_topology X := ⟨rfl⟩; apply_instance },
  map := λ X Y f, by letI:topological_space X := ⊥; letI:discrete_topology X := ⟨rfl⟩;
                  by letI:topological_space Y := ⊥; letI:discrete_topology Y := ⟨rfl⟩;
                  exact ⟨f, continuous_of_discrete_topology⟩ }

namespace Profinite

open category_theory.limits

variable {J : Type*}
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


variables {α : Type*} [topological_space α]
open set
local attribute [instance] component_setoid

--
lemma component_nrel_iff {x y : α} : ⟦x⟧ ≠ ⟦y⟧ ↔ connected_component x ≠ connected_component y :=
begin
rw not_iff_not,
exact component_rel_iff,
end

lemma clopen_eq_union_connected_components {Z : set α} (h : is_clopen Z) :
  Z = (⋃ (x : α) (H : x ∈ Z), connected_component x) :=
begin
  apply eq_of_subset_of_subset,
  { intros x xZ,
    apply mem_Union.2 ⟨x, _⟩,
    apply mem_Union.2,
    use xZ,
    exact mem_connected_component,
  },
  apply Union_subset,
  intro x,
  apply Union_subset,
  intro xZ,
  apply subset.trans connected_component_subset_Inter_clopen (Inter_subset _ ⟨Z, ⟨h, xZ⟩⟩),
end

-- TODO USE IMAGE_CONNECTED_COMPONENT TO REWRITE LATER PROOF

-- todo reduce to nonempty fibers
-- TODO: use...
lemma surjective_of_connected_fibers {β : Type*} [topological_space β] {f : α → β}
  (connected_fibers : ∀ t : β, is_connected (f ⁻¹' {t})) : function.surjective f :=
begin
  intro t,
  choose s hs using (connected_fibers t).1,
  use s,
  rw mem_preimage at hs,
  apply hs,
end

#check mem_preimage

-- Version of stacks 0377
-- TODO: better naming
lemma connected_bij {β : Type*} [topological_space β] {f : α → β}
  (connected_fibers : ∀ t : β, is_connected (f ⁻¹' {t}))
  (hcl : ∀ (T : set β), is_closed T ↔ is_closed (f ⁻¹' T)) :
  ∀ t : β, is_preconnected (f ⁻¹' connected_component t) :=
begin
  intro t,
  -- T closed
  have hT : is_closed (f ⁻¹' connected_component t),
  { apply (hcl (connected_component t)).1,
    apply is_closed_connected_component },
  apply (is_preconnected_iff_subset_of_fully_disjoint_closed hT).2,
  intros u v hu hv huv uv_disj,

  -- TODO: move out?
  have HH : ∀ t' ∈ connected_component t, f ⁻¹' {t'} ⊆ f ⁻¹' connected_component t,
  { intros t' ht',
    apply (preimage_subset_preimage_iff _).2 (singleton_subset_iff.2 ht'),
    rw [singleton_subset_iff, mem_range],
    choose s hs using (connected_fibers t').1,
    use s,
    rw mem_preimage at hs,
    apply hs },

  -- TODO: rename
  have h_decomp : ∀ t' ∈ connected_component t, f ⁻¹' {t'} ⊆ u ∨ f ⁻¹' {t'} ⊆ v,
  { intros t' ht',
    apply is_preconnected_iff_subset_of_disjoint_closed.1 (connected_fibers t').2 u v hu hv,
    { apply subset.trans _ huv,
      apply HH t' ht'},
    rw uv_disj,
    exact inter_empty _,
  },
  let T₁ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ u },
  let T₂ := {t' ∈ connected_component t | f ⁻¹' {t'} ⊆ v },

  have T₁_u :  f ⁻¹' T₁ =  (f ⁻¹' connected_component t) ∩ u,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      apply bUnion_subset,
      intros t' ht',
      apply subset_inter _ ht'.2,
      apply HH t' ht'.1 },
    intros a ha,
    cases ha with hat hau,
    constructor,
    { apply mem_preimage.1 hat },
    simp,
    cases h_decomp (f a) (mem_preimage.1 hat),
    { apply h },
    { exfalso,
      have hav : a ∈ v,
      -- tidy proof
      { cases hat, cases hat_h, cases hat_h_w, solve_by_elim },
      rw ←not_nonempty_iff_eq_empty at uv_disj,
      apply uv_disj,
      apply nonempty_of_mem (mem_inter hau hav) } },
  -- TODO: same proof as T₁_u.... Move out?
  have T₂_v :  f ⁻¹' T₂ =  (f ⁻¹' connected_component t) ∩ v,
  { apply eq_of_subset_of_subset,
    { rw ←bUnion_preimage_singleton,
      apply bUnion_subset,
      intros t' ht',
      apply subset_inter _ ht'.2,
      apply HH t' ht'.1 },
    intros a ha,
    cases ha with hat hav,
    constructor,
    { apply mem_preimage.1 hat },
    simp,
    cases h_decomp (f a) (mem_preimage.1 hat),
    { exfalso,
      have hau : a ∈ u,
      -- tidy proof
      { cases hat, cases hat_h, cases hat_h_w, solve_by_elim },
      rw ←not_nonempty_iff_eq_empty at uv_disj,
      apply uv_disj,
      apply nonempty_of_mem (mem_inter hau hav) },
    { apply h }},

  have hT₁ : is_closed T₁,
  { apply (hcl T₁).2,
    rw T₁_u,
    apply is_closed_inter hT hu},
  have hT₂ : is_closed T₂,
  { apply (hcl T₂).2,
    rw T₂_v,
    apply is_closed_inter hT hv},
  -- TODO, possibly only need 1 direction
  have T_decomp : (connected_component t) ⊆ T₁ ∪ T₂,
  { intros t' ht',
    apply (mem_union t' T₁ T₂).2,
    cases h_decomp t' ht' with htu htv,
    { left, exact ⟨ht', htu⟩ },
    right, exact ⟨ht', htv⟩ },
  -- show Ti are disjoint
  have T_disjoint : T₁ ∩ T₂ = ∅,
  -- TODO
  { have asdf : f ⁻¹' T₁ ∩ f ⁻¹' T₂ = ∅,
    { rw [T₁_u, T₂_v],
      rw inter_comm at uv_disj,
      conv
      begin
        congr,
        rw [inter_assoc],
        congr, skip,
        rw [←inter_assoc, inter_comm, ←inter_assoc],
        rw [uv_disj, empty_inter],
      end,
      apply inter_empty },
    -- TODO: fix proof.
    rw ←preimage_inter at asdf,
    rw ←(image_preimage_eq (T₁ ∩ T₂) (surjective_of_connected_fibers connected_fibers)),
    rw asdf,
    apply image_empty },
  -- show T is a subset of either
  have HHH := (is_preconnected_iff_subset_of_fully_disjoint_closed is_closed_connected_component).1
    (is_connected_connected_component).2 T₁ T₂ hT₁ hT₂ T_decomp T_disjoint,
  cases HHH,
  { left,
    rw subset.antisymm_iff at T₁_u,
    suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₁,
    { exact (subset.trans (subset.trans this T₁_u.1) (inter_subset_right _ _)) },
    apply preimage_mono HHH,
  },
  right,
  rw subset.antisymm_iff at T₂_v,
  suffices : f ⁻¹' connected_component t ⊆ f ⁻¹' T₂,
  { exact (subset.trans (subset.trans this T₂_v.1) (inter_subset_right _ _)) },
  apply preimage_mono HHH,
end

--
lemma preimage_singleton_pi0 {t : α} : connected_component t = quotient.mk ⁻¹' {⟦t⟧} :=
begin
  apply set.eq_of_subset_of_subset,
  { intros a ha,
    rw mem_preimage,
    have H : ⟦a⟧ = ⟦t⟧,
    { rw component_rel_iff,
      exact eq.symm (connected_component_eq ha) },
    rw H,
    exact mem_singleton ⟦t⟧ },
  intros a ha,
  rw mem_preimage at ha,
  simp only [mem_singleton_iff, component_rel_iff] at ha,
  rw ←ha,
  exact mem_connected_component,
end

-- TODO: potentially incorporate into theorem? Or better naming
lemma preimage_image_pi0 (U : set α) :
  quotient.mk ⁻¹' (quotient.mk '' U) = ⋃ (x : α) (h : x ∈ U), connected_component x :=
begin
  apply set.eq_of_subset_of_subset,
  { intros a ha,
    rw mem_preimage at ha,
    rw mem_image _ _ ⟦a⟧ at ha,
    rcases ha with ⟨b, hb, hab⟩,
    apply mem_Union.2, use b,
    apply mem_Union.2, use hb,
    rw component_rel_iff at hab,
    rw hab,
    exact mem_connected_component },
  apply Union_subset, intro a,
  apply Union_subset, intro ha,
  rw preimage_singleton_pi0,
  rw (function.surjective.preimage_subset_preimage_iff (surjective_quotient_mk _)),
  rw singleton_subset_iff,
  rw mem_image, use a,
  exact ⟨ha , refl _⟩,
end

instance pi0.totally_disconnected_space :
  totally_disconnected_space (π₀ α) :=
begin
  rw totally_disconnected_space_iff_connected_component_subsingleton,
  intro x,
  apply quotient.induction_on x,
  intro a,
  constructor,
  intros x' x'',
  cases x',
  cases x'',
  revert x'_property,
  revert x''_property,
  apply quotient.induction_on x'_val,
  apply quotient.induction_on x''_val,
  intros b c hb hc,
  ext,
  dsimp,
  rw component_rel_iff,
  rw ←mem_preimage at hb,
  have H : is_preconnected (quotient.mk ⁻¹' connected_component ⟦a⟧),
  { apply connected_bij,
    { intro t,
      apply quotient.induction_on t,
      intro s,
      rw ←preimage_singleton_pi0,
      exact is_connected_connected_component,
    },
    intro T,
    split,
    { exact λ hT, is_closed.preimage (continuous_quotient_mk) hT },
    intro hT,
    rw [←is_open_compl_iff, ←preimage_compl] at hT,
    rw [←is_open_compl_iff, ←(quotient_map.is_open_preimage quotient_map_quotient_mk)],
    exact hT,
  },
  have h1 := subset_connected_component H hb,
  rw ←mem_preimage at hc,
  apply eq.symm,
  apply connected_component_eq,
  apply mem_of_subset_of_mem h1 hc,
end

instance pi0.t2 [t2_space α] [compact_space α]: t2_space (π₀ α) :=
begin
  -- Fix 2 distinct connected components, with points a and b
  constructor, intros x y,
  apply quotient.induction_on x,
  apply quotient.induction_on y,
  intros a b ne,
  rw component_nrel_iff at ne,
  have h := connected_component_disjoint ne,
  -- write ⟦b⟧ as the intersection of all clopen subsets containing it
  rw [connected_component_eq_Inter_clopen, disjoint_iff_inter_eq_empty, inter_comm] at h,
  -- Now we show that this can be reduced to some clopen containing ⟦b⟧ being disjoint to ⟦a⟧
  cases is_compact.elim_finite_subfamily_closed
    (is_closed.compact (is_closed_connected_component)) _ _ h with fin_a ha,
  -- TODO... possible to incorporate in line above?
  swap, exact (λ Z, Z.2.1.2),
  set U : set α := (⋂ (i : {Z // is_clopen Z ∧ b ∈ Z}) (H : i ∈ fin_a), ↑i) with hU,
  have hu_clopen : is_clopen U, { apply is_clopen_bInter _, exact (λ i j, i.2.1) },
  rw ←hU at ha,
  -- This clopen and its complement will separate the points corresponding to ⟦a⟧ and ⟦b⟧
  use quotient.mk '' U,
  use quotient.mk '' Uᶜ,
  -- Using the fact that clopens are unions of connected components, we show that
  -- U and Uᶜ is the preimage of a clopen set in the quotient
  -- TODO: renaming
  have h1 := clopen_eq_union_connected_components hu_clopen,
  have h2 : (quotient.mk ⁻¹' (quotient.mk '' U)) = U,
  { rw preimage_image_pi0,
    exact eq.symm h1 },
  have h3 : (quotient.mk ⁻¹' (quotient.mk '' Uᶜ)) = Uᶜ,
  { rw preimage_image_pi0,
    exact eq.symm (clopen_eq_union_connected_components (is_clopen_compl hu_clopen)) },
  -- showing that U and Uᶜ are open and separates ⟦a⟧ and ⟦b⟧
  -- TODO, can I avoid all these splits?
  split,
  {  apply ((quotient_map_iff.1 quotient_map_quotient_mk).2 _).2,
      rw h2,
      exact hu_clopen.1 },
  split,
  { apply ((quotient_map_iff.1 quotient_map_quotient_mk).2 _).2,
    rw h3,
    exact is_open_compl_iff.2 hu_clopen.2 },
  split,
  { apply mem_image_of_mem,
    rw mem_Inter, intro Z,
    rw mem_Inter, intro Zmem,
    exact Z.2.2 },
  split,
  { apply mem_image_of_mem,
    apply mem_of_subset_of_mem _ (@mem_connected_component _ _ a),
    exact subset_compl_iff_disjoint.2 ha },
  apply preimage_injective.2 (@surjective_quotient_mk _ _),
  rw [preimage_inter, preimage_empty, h2, h3, inter_compl_self _],
end

-- Stacks tag 09000
def CompHaus_to_Profinite : CompHaus ⥤ Profinite :=
{ obj := λ X,
    { to_Top := { α := (π₀ X.to_Top.α) } },
  map := λ X Y f,
    { to_fun := pi0_map f.1 f.2,
    continuous_to_fun := continuous_quotient_lift _ (continuous.comp (continuous_quotient_mk) f.2)}}
    -- possible TODO: pi0_map.continuous

instance : is_right_adjoint Profinite_to_CompHaus :=
{ left := CompHaus_to_Profinite,
  adj :=
    { hom_equiv := λ X Y,
      { to_fun := λ f,
        { to_fun := f.1 ∘ quotient.mk,
          continuous_to_fun := continuous.comp f.2 (continuous_quotient_mk) },
        inv_fun := λ g,
        { to_fun := pi0.lift g.1 g.2,
          continuous_to_fun := pi0.lift.continuous g.1 g.2 },
  -- TODO: REMOVE BAD TIDY CODE
        left_inv := by {intros x, dsimp at *, simp at *, ext1, induction x_1,
          work_on_goal 0 { refl }, refl},
        right_inv := by {intros x, dsimp at *, simp at *, ext1, refl}},
    unit :=
    { app := λ X,
      begin
        simp only [functor.id_obj, functor.comp_obj],
        exact { to_fun := quotient.mk,
                continuous_to_fun := continuous_quotient_mk },
      end
    },
    counit :=
      { app := λ Y,
      begin
        simp only [functor.id_obj, functor.comp_obj],
        fsplit,
        { change ((π₀ Y.to_Top.α) → Y.to_Top.α),
          apply pi0.lift (𝟙 Y.to_Top),
          -- TODO: FIX
          dsimp at *, fsplit, intros s ᾰ, assumption},
        -- TODO: FIX
        dsimp at *, simp at *, fsplit, intros s ᾰ, assumption,
      end}}}

instance : reflective Profinite_to_CompHaus :=
{ .. Profinite_to_CompHaus.category_theory.is_right_adjoint,
  .. Profinite_to_CompHaus.category_theory.full,
  .. Profinite_to_CompHaus.category_theory.faithful}

#check Profinite_to_CompHaus.category_theory.reflective

/-
{ right_adjoint_proof := by apply_instance,
  full_proof := by apply_instance,
  faithful_proof := by apply_instance } -/

-- inductive finite_jointly_surjective (Y : Profinite)
-- | mk {ι : Type*} [fintype ι] (X : ι → Profinite) (f : Π (i : ι), X i ⟶ Y)
--      (hf : ∀ (y : Y), ∃ (i : ι) (x : X i), f i x = y) :
--     finite_jointly_surjective Y

inductive presieve_of_arrows {X : Profinite} {ι : Type*} (Y : ι → Profinite) (f : Π i, Y i ⟶ X) :
  presieve X
| mk {i : ι} : presieve_of_arrows (f i)

def proetale_pretopology : pretopology Profinite :=
{ coverings := λ X S, ∃ (ι : Type*) [fintype ι] (Y : ι → Profinite) (f : Π (i : ι), Y i ⟶ X),
      (∀ (x : X), ∃ i y, f i y = x) ∧ S = presieve_of_arrows Y f,
  has_isos := λ X Y f i,
  begin
    refine ⟨punit, infer_instance, λ _, Y, λ _, f, _, _⟩,
    intro x,
    refine ⟨punit.star, _, _⟩,
    resetI,
    apply (forget _).map (inv f) x,
    dsimp,
    sorry,
    ext Y g,
    split,
    { rintro ⟨_⟩,
      apply presieve_of_arrows.mk,
      apply punit.star },
    { rintro ⟨_⟩,
      apply presieve.singleton.mk },
  end,
  pullbacks := λ X Y f S,
  begin
    rintro ⟨ι, hι, Z, g, hg, rfl⟩,
    refine ⟨ι, hι, λ i, pullback (g i) f, λ i, pullback.snd, _, _⟩,
    intro y,
    rcases hg (f y) with ⟨i, z, hz⟩,
    refine ⟨i, _, _⟩,
    sorry, sorry,
    ext W k,
    split,
    { intro hk,
      cases hk with W k hk₁,
      cases hk₁ with i hi,
      apply presieve_of_arrows.mk },
    { intro hk,
      cases hk with i,
      apply pullback_arrows.mk,
      apply presieve_of_arrows.mk }
  end,
  transitive := λ X S Ti,
  begin
    rintro ⟨ι, hι, Z, g, hY, rfl⟩ hTi,
    choose j hj W k hk₁ hk₂ using hTi,
    refine ⟨Σ (i : ι), j (g i) presieve_of_arrows.mk, _, λ ij, W _ _ ij.2, _, _, _⟩,
    { apply sigma.fintype _,
      { apply hι },
      { intro i,
        apply hj } },
    { intro ij,
      apply k _ _ ij.2 ≫ g ij.1 },
    { intro x,
      rcases hY x with ⟨i, y, hy⟩,
      rcases hk₁ (g i) presieve_of_arrows.mk y with ⟨j', z, hz⟩,
      refine ⟨⟨i, j'⟩, z, _⟩,
      rw ← hy,
      rw ← hz,
      refl },
    { ext Y f,
      split,
      { sorry },
      { sorry } }
  end }



/-

{ sieves := λ A, {S | ∀ x, ∃ B (f : B ⟶ A) b, S.arrows f ∧ f b = x},
  top_mem' := λ A, (λ x, by {use A, use (𝟙 A), use x, split, work_on_goal 0 { exact dec_trivial }, refl,}),
  pullback_stable' := λ X Y S f h, (λ y,
    begin
      cases h (f y),
    end),
  transitive' := _ }




lemma profinite_is_limit_of_discrete {ι : Type*} (I : ι → Type) (h : ∀ i, fintype (I i)) (X : Profinite) : _
-/
end Profinite
