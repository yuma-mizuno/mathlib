/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import category_theory.sites.pretopology

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

#check limits.is_limit.of_faithful

namespace Profinite

variables (α : Type*) [topological_space α]

open category_theory.limits

--def limit_aux
#check continuous_apply
-- λp:Πi, π i, p i
variable {J : Type*}

/-
totally_disconnected_space ↥{α := Π (i : J), ↥(F.obj i),
str := Pi.topological_space (λ (a : J), (F.obj a).to_Top.topological_space)
-/

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

def proetale_pretopology : pretopology Profinite :=
{ coverings := λ X, {S | (∀ x, ∃ Y (f : Y ⟶ X) y, S f ∧ f y = x) ∧
                         set.finite {Y | nonempty {f : Y ⟶ X | S f}} ∧
                         ∀ Y, set.finite {f : Y ⟶ X | S f}},
  has_isos := λ X Y f i,
  begin
    resetI,
    refine ⟨λ z, ⟨_, f, inv ((forget _).map f) z, presieve.singleton_self _, congr_fun (is_iso.inv_hom_id ((forget Profinite).map f)) z⟩, _, _⟩,
    { let k := {Y_1 : Profinite | nonempty ↥{f_1 : Y_1 ⟶ X | presieve.singleton f f_1}},
      change k.finite,
      suffices : k = {Y},
        rw this,
        refine set.finite_singleton Y,

    }
  end,
  pullbacks := _,
  transitive := _ }

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
