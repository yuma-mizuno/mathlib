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

def component_setoid (α : Type*) [topological_space α] : setoid α :=
⟨ λ x y, connected_component y = connected_component x,
  ⟨ λ x, by trivial, λ x y h1, eq.symm h1, λ x y z h1 h2, eq.trans h2 h1 ⟩⟩
local attribute [instance] component_setoid

variables {α : Type*} [topological_space α]
open set

lemma component_rel_iff {x y : α} : ⟦x⟧ = ⟦y⟧ ↔ connected_component x = connected_component y :=
⟨λ h, (quotient.exact h).symm, λ h, quotient.sound h.symm⟩

#check subset_connected_component
#check not_iff_not

lemma connected_component_disjoint {x y : α} (h : connected_component x ≠ connected_component y) :
  disjoint (connected_component x) (connected_component y) :=
set.disjoint_left.2 (λ a h1 h2, h (
  eq.trans (connected_component_eq h1) (connected_component_eq h2).symm))

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

lemma totally_disconnected_space_iff_connected_component_singleton :
  totally_disconnected_space α ↔ (∀ x : α, subsingleton (connected_component x)) :=
begin
  split,
  { intros h x,
    apply h.1,
    { apply subset_univ },
    exact (is_connected_connected_component).2 },
  intro h, constructor,
  intros s s_sub hs,
  -- TODO subsingleton of subtype
  sorry,
end

#check is_clopen_inter_of_disjoint_cover_clopen
#check is_closed.preimage

instance component_quot.totally_disconnected_space :
  totally_disconnected_space (quotient (component_setoid α)) :=
begin
  rw totally_disconnected_space_iff_connected_component_singleton,
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
  have H : is_connected (quotient.mk ⁻¹' connected_component ⟦a⟧),
  { refine ⟨nonempty_of_mem hb, _⟩,
    apply (is_preconnected_iff_subset_of_fully_disjoint_closed
      (is_closed.preimage continuous_quotient_mk is_closed_connected_component)).2,
    intros u v hu hv uv_cover huv,
    let T₁ := {t : quotient (component_setoid α) | (t ∈ connected_component ⟦a⟧) ∧ (quotient.mk ⁻¹ t) ⊆ u},
    let T₂ := {t : quotient (component_setoid α) | (t ∈ connected_component ⟦a⟧) ∧ (quotient.mk ⁻¹ t) ⊆ v},
    have H1 : connected_component ⟦a⟧ = T₁ ∪ T₂,
    { apply set.eq_of_subset_of_subset,
      { sorry

      },
      sorry
    },
    have HT₁ : is_closed T₁,
    {

    },
    have HT₂ : is_closed T₂,
    {

    },
    /-
    some Ti = ∅
    connected_component ⟦a⟧ = Ti → subset thing.. DONE
    ...

    -/
    sorry,
  },

  have h1 := subset_connected_component H.2 hb,
  rw ←mem_preimage at hc,
  apply eq.symm,
  apply connected_component_eq,
  apply mem_of_subset_of_mem h1 hc,
end

#check quotient.lift
#check function.comp
#check quotient.sound
#check quotient
#check is_preconnected.image
#check component_rel_iff

def component_map {β : Type*} [topological_space β] (f : α → β) [h : continuous f] :
  quotient (component_setoid α) → quotient (component_setoid β) :=
quotient.lift (quotient.mk ∘ f) (λ a b hab,
begin
  apply quotient.sound,
  apply connected_component_eq,
  -- TODO: make separate lemma:
  have H : f '' connected_component b ⊆ connected_component (f b),
  { apply subset_connected_component,
    { exact is_preconnected.image (is_connected_connected_component).2 f (continuous.continuous_on h)},
    rw mem_image,
    use b,
    split,
    { exact mem_connected_component },
    refl,
  },
  apply mem_of_subset_of_mem H,
  rw mem_image,
  use a,
  split,
  { rw ←(component_rel_iff.1 (quotient.sound hab)),
    exact mem_connected_component },
  refl,
end
)



#check quotient_map_iff.1
#check is_compact.inter_Inter_nonempty
#check is_compact.elim_finite_subfamily_closed
#check subset_preimage_image
#check preimage_injective
#check preimage_empty

def CompHaus_to_Profinite : CompHaus ⥤ Profinite :=
{ obj := λ X,
  { to_Top := { α := quotient (component_setoid X.to_Top.α)},
    is_compact := quotient.compact_space,
    is_t2 :=
    begin
      constructor, intros x y,
      apply quotient.induction_on x,
      apply quotient.induction_on y,
      intros a b ne,
      rw component_nrel_iff at ne,
      have h := connected_component_disjoint ne,
      rw [connected_component_eq_Inter_clopen, disjoint_iff_inter_eq_empty, inter_comm] at h,
      cases is_compact.elim_finite_subfamily_closed
        (is_closed.compact (is_closed_connected_component)) _ _ h with fin_a ha,
      simp at ha,
      set U : set X.to_Top.α := (⋂ (i : {Z // is_clopen Z ∧ b ∈ Z}) (H : i ∈ fin_a), ↑i) with hU,
      rw ←hU at ha,
      use quotient.mk '' U,
      use quotient.mk '' Uᶜ,
      have hu : is_clopen U, { apply is_clopen_bInter _, exact (λ i j, i.2.1) },
      have h1 := clopen_eq_union_connected_components hu,
      have h2 : (quotient.mk ⁻¹' (quotient.mk '' U)) = U,
      { apply set.eq_of_subset_of_subset,
        { conv {congr, skip, rw h1},
          intros c hc,
          rw mem_preimage at hc,
          rw mem_image _ _ ⟦c⟧ at hc,
          rcases hc with ⟨d, hd, hcd⟩,
          apply mem_Union.2, use d,
          apply mem_Union.2, use hd,
          rw component_rel_iff at hcd,
          rw hcd,
          exact mem_connected_component },
        exact subset_preimage_image _ _ },
      have h3 : (quotient.mk ⁻¹' (quotient.mk '' Uᶜ)) = Uᶜ,
      { --TODO : make h2 into lemma and apply here
        sorry },
      split,
      {  apply ((quotient_map_iff.1 quotient_map_quotient_mk).2 _).2,
         rw h2,
         exact hu.1 },
      split,
      { apply ((quotient_map_iff.1 quotient_map_quotient_mk).2 _).2,
        rw h3,
        exact is_open_compl_iff.2 hu.2 },
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
      -- TOO SWAP GOAL TO AFTER have ha
      exact (λ Z, Z.2.1.2),
    end
    },
  map := _,}

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
