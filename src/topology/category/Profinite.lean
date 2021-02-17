/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import category_theory.sites.pretopology
import category_theory.Fintype
import topology.connected
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
                convert (_:
                  is_closed (⋂ (j j' : J) (f : j ⟶ j'), {u : Π j, F.obj j | F.map f (u j) = u j'})),
                { ext1,
                  simp only [forall_apply_eq_imp_iff', set.mem_sInter, set.mem_range,
                            set.mem_Inter, set.mem_set_of_eq, exists_imp_distrib],
                  refl },
                exact (
                  is_closed_Inter (λ j, is_closed_Inter (λ j', is_closed_Inter
                    (λ f, is_closed_eq ((F.map f).2.comp (continuous_apply _))
                      (continuous_apply _))))),
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

--def prof_limit_skeleton (X : Profinite) : set (set (topological_space.opens X.to_Top.α)) :=
--{ I | (⋃ (u : I), ↥u) = X.to_Top.α }

universe u
open set
open topological_space
open category_theory.limits

-- https://stacks.math.columbia.edu/tag/08ZY

/-
In this section we formalize that a profinite set can be seen as a limit of finite sets by
following: https://stacks.math.columbia.edu/tag/08ZY
-/

/-- (Implementation) The skeleton, i.e. the points, of the diagram which X is the limit of -/
def profinite_skeleton (X : Profinite) :=
{ I : set (set (X.to_Top.α)) | (I.finite) ∧ (∀ U ∈ I, is_open U ∧ U.nonempty) ∧
  (⋃₀ I = univ) ∧ (∀ U V ∈ I, (U ∩ V : set X.to_Top.α).nonempty → (U = V) )}

variable {X : Profinite}

lemma refinement_unique {I J : profinite_skeleton X} {U V W : set X.to_Top.α} (hU : U ∈ I.1)
  (hV : V ∈ J.1) (hW : W ∈ J.1) (hUV : U ⊆ V) (hUW : U ⊆ W) : V = W :=
J.2.2.2.2 V W hV hW (nonempty.mono (subset_inter hUV hUW) (I.2.2.1 U hU).2)

/-- (Implementation) profinite_skeleton forms a partial order-/
instance profinite_skeleton.partial_order : partial_order (profinite_skeleton X) :=
{ le := λ I J, (∀ (U ∈ I.1), (∃ V : set X.to_Top.α, V ∈ J.1 ∧ U ⊆ V)),
  le_refl := λ I U hU, exists.intro U ⟨hU, subset.refl U⟩,
  le_trans :=
  begin
    intros I J K hIJ hJK U hU,
    rcases hIJ U hU with ⟨V, hV, hUV⟩,
    rcases hJK V hV with ⟨W, hW, hVW⟩,
    use W,
    exact ⟨hW, subset.trans hUV hVW⟩,
  end,
  -- TODO: do we even need partial order? is preorder enough?
  le_antisymm :=
  begin
    intros I J hIJ hJI,
    ext U,
    split; intro hU,
    { rcases hIJ U hU with ⟨V, ⟨hV, hUV⟩⟩,
      rcases hJI V hV with ⟨W, ⟨hW, hVW⟩⟩,
      have H := refinement_unique hU hU hW (subset.refl U) (subset.trans hUV hVW),
      rw ←H at hVW,
      rwa eq_of_subset_of_subset hUV hVW },

    rcases hJI U hU with ⟨V, ⟨hV, hUV⟩⟩,
    rcases hIJ V hV with ⟨W, ⟨hW, hVW⟩⟩,
    have H := refinement_unique hU hU hW (subset.refl U) (subset.trans hUV hVW),
    rw ←H at hVW,
    rwa eq_of_subset_of_subset hUV hVW,
  end }

-- TODO: MAKE SURE the right ≤ is the one used!!

/-- profinite_skeleton forms a category, this will be the codomain of our diagram -/
instance profinite_limit_category : small_category (profinite_skeleton X) :=
@preorder.small_category _ (@partial_order.to_preorder _ profinite_skeleton.partial_order)

/-
To define our diagram we first make a short API in order to work with the associated maps
on objects and morphisms
-/



/-- Map on objects of profinite_diagram -/
noncomputable def profinite_diagram_obj (I : profinite_skeleton X) : Fintype :=
{ α := I,
  str := finite.fintype I.2.1 }

@[simp]
lemma profinite_diagram_obj_eq (I : profinite_skeleton X) : (profinite_diagram_obj I).1 = I := rfl

lemma profinite_diagram_obj' {I : profinite_skeleton X} (U : (profinite_diagram_obj I).α) :
U.1 ∈ I.1 := U.2

-- TODO: termmode????
/-- Map on morphisms of profinite_diagram-/
def profinite_diagram_map {I J : profinite_skeleton X} (f : I ⟶ J) :
  (profinite_diagram_obj I) ⟶ (profinite_diagram_obj J) :=
by {exact λ U, ⟨(classical.some (f.1.1 U.1 U.2)), (classical.some_spec (f.1.1 U.1 U.2)).1⟩}

@[simp]
lemma profinite_diagram_map_sub {I J : profinite_skeleton X} (f : I ⟶ J)
  (U : (profinite_diagram_obj I).α) : U.1 ⊆ (profinite_diagram_map f U).1 :=
(classical.some_spec (f.1.1 U.1 U.2)).2

@[simp]
lemma profinite_diagram_map_unique {I J : profinite_skeleton X} (f : I ⟶ J)
  (U : (profinite_diagram_obj I).α) (V : (profinite_diagram_obj J).α)
  (hUV : U.1 ⊆ V.1) : profinite_diagram_map f U = V :=
subtype.ext $
  refinement_unique U.2 (profinite_diagram_map f U).2 V.2 (profinite_diagram_map_sub f U) hUV

/-- The diagram into Fintype associated to X -/
noncomputable def profinite_diagram' (X : Profinite) : profinite_skeleton X ⥤ Fintype :=
{ obj := profinite_diagram_obj,
  map := λ I J, @profinite_diagram_map X I J,
  map_id' := by {refine λ I, funext (λ U, profinite_diagram_map_unique _ _ _ (subset.refl U.1)) },
  map_comp' :=
  begin
    refine λ I J K f g, funext (λ U, profinite_diagram_map_unique _ _ _ _),
    -- TODO: change this line
    change U.val ⊆ ((profinite_diagram_map g) ((profinite_diagram_map f) U)).1,
    exact subset.trans (profinite_diagram_map_sub f U) (profinite_diagram_map_sub g _),
  end, }

/-- The diagram of which a given profinite set is the limit of -/
noncomputable def profinite_diagram (X : Profinite) : profinite_skeleton X ⥤ Profinite :=
(profinite_diagram' X) ⋙ Fintype_to_Profinite

lemma profinite_diagram.map {X : Profinite} {I J : profinite_skeleton X} (f : I ⟶ J) :
  (X.profinite_diagram.map f).to_fun = (profinite_diagram_map f) := rfl

/-
Now we create an API for the maps making X into a cone over profinite_diagram
-/


/-- Map from X to a given object of the diagram -/
def X_to_partition_map (I : profinite_skeleton X) : X → (profinite_diagram_obj I) :=
λ x, by { have H := mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1),
  exact ⟨classical.some H, classical.some (classical.some_spec H)⟩ }

-- TODO: renaming
lemma component_unique' (I : profinite_skeleton X) {x : X} {U V: set X} (hU : U ∈ I.1)
  (hV : V ∈ I.1) (hxU : x ∈ U) (hxV : x ∈ V) : U = V :=
I.2.2.2.2 U V hU hV (nonempty_of_mem (mem_inter hxU hxV))

lemma X_to_partition_map_mem' (I : profinite_skeleton X) (x : X) :
  (X_to_partition_map I x).1 ∈ I.1 :=
classical.some (classical.some_spec (mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1)))

lemma X_to_partition_map_point_mem (I : profinite_skeleton X) (x : X) : x ∈ (X_to_partition_map I x).1 :=
classical.some_spec $ classical.some_spec
  (mem_sUnion.1 ((I.2.2.2.1).symm ▸ (mem_univ x) : x ∈ ⋃₀ I.1))

lemma X_to_partition_map_unique (I : profinite_skeleton X) (x : X) (U : set X) (hU : U ∈ I.1)
  (hx : x ∈ U) : (X_to_partition_map I x).1 = U :=
component_unique' I (X_to_partition_map_mem' I x) hU (X_to_partition_map_point_mem I x) hx

lemma X_to_partition_map_preimage (I : profinite_skeleton X) (A : set (profinite_diagram_obj I)) :
  (X_to_partition_map I ⁻¹' A) = ⋃ (a : A), a.1.1 :=
begin
  refine set.ext (λ x, ⟨λ hx, _ , λ hx, _⟩),
  -- TODO: golf
  { rw mem_Union,
    use X_to_partition_map I x,
    { exact mem_preimage.1 hx },
    exact X_to_partition_map_point_mem I x },
  rcases mem_Union.1 hx with ⟨⟨U, hU⟩, hx⟩,
  rw [mem_preimage],
  suffices : X_to_partition_map I x = U,
  { rw this, exact hU },
  apply subtype.ext,
  apply (X_to_partition_map_unique I x U.1 U.2 hx),
end

/-- X forms a cone over profinite_diagram -/
noncomputable def profinite_limit_cone (X : Profinite) : cone (profinite_diagram X) :=
{ X := X,
  π :=
  { app := λ I,
    { to_fun := X_to_partition_map I,
      continuous_to_fun :=
      begin
        fsplit,
        -- A is a set of "opens in I"
        intros A hA,
        rw X_to_partition_map_preimage,
        refine is_open_Union (λ U, _),
        exact (I.2.2.1 U.1.1 U.1.2).1,
      end },
    naturality' := sorry } }


/-
Now we make an API for the limit of profinite_diagram and its lifts
-/

/-- Limit object over profinite_diagram -/
noncomputable def profinite_limit (X : Profinite) : Profinite :=
  (limit_cone (profinite_diagram X)).X

/-- Map from X to the limit of profinite_diagram -/
noncomputable def profinite_limit_map (X : Profinite) : X ⟶ profinite_limit X :=
(limit_cone_is_limit (profinite_diagram X)).lift (profinite_limit_cone X)

lemma profinite_limit.α (X : Profinite) : ↥(profinite_limit X).to_Top =
{ u : Π (I : profinite_skeleton X), (profinite_diagram X).obj I // ∀ {I J} (f : I ⟶ J),
  (profinite_diagram X).map f (u I) = (u J)} := rfl

/-- Explicit form of the map from X to the limit of profinite_diagram -/
def profinite_limit.image_elem {X : Profinite} (x : X) :
  (profinite_limit X).to_Top.α :=
⟨(λ I, X_to_partition_map I x), λ I J f, subtype.ext $ eq.symm $ X_to_partition_map_unique J x
  (profinite_diagram_map f (X_to_partition_map I x)).1
  (profinite_diagram_map f (X_to_partition_map I x)).2
  (mem_of_subset_of_mem (profinite_diagram_map_sub _ _) (X_to_partition_map_point_mem I x))⟩

lemma profinite_limit_map_elem {X : Profinite} (x : X) :
  (X.profinite_limit_map).1 x = profinite_limit.image_elem x := rfl

/-
As in https://stacks.math.columbia.edu/tag/08ZY, what remains now is to show
that profinite_limit_map is a homeomorphism.

First we show injectivity, to do this we make a short API for defining points of.....
-/
-- TODO: naming
def profinite_limit_map.obj {X : Profinite} {Z : set X.to_Top.α} (hZ : is_clopen Z)
  (hZ_ne : Z.nonempty) (hZ_compl : Zᶜ.nonempty) : profinite_skeleton X :=
begin
  refine ⟨{Z, Zᶜ}, ⟨_,_,_,_⟩⟩,
  { simp only [finite.insert, finite_singleton] },
  { rintros U ⟨hU, _⟩,
    { refine ⟨hZ.1, hZ_ne⟩ },
    rw mem_singleton_iff at H,
    rw H,
    refine ⟨is_open_compl_iff.2 hZ.2, hZ_compl⟩ },
  { simp only [sUnion_singleton, union_compl_self, sUnion_insert] },
  intros U V hU hV hUV,
    cases hU with hU hU,
    { cases hV with hV hV,
      { rwa [hU, hV] },
      rw mem_singleton_iff at hV,
      rw [hU, hV, inter_compl_self] at hUV,
      exfalso,
      revert hUV,
      exact empty_not_nonempty },
    rw mem_singleton_iff at hU,
    cases hV with hV hV,
    { rw [hU, hV, inter_comm, inter_compl_self] at hUV,
      exfalso,
      revert hUV,
      exact empty_not_nonempty },
    rw mem_singleton_iff at hV,
    rwa [hU, hV],
end

lemma profinite_limit_map.obj_val {X : Profinite} {Z : set X.to_Top.α} (hZ : is_clopen Z)
  (hZ_ne : Z.nonempty) (hZ_compl : Zᶜ.nonempty) :
  (profinite_limit_map.obj hZ hZ_ne hZ_compl).1 = {Z, Zᶜ} := rfl


lemma profinite_limit_map.mem {X : Profinite} {x y : X} {Z : set X.to_Top.α} (hZ : is_clopen Z)
  (hxy : (X.profinite_limit_map).1 x = (X.profinite_limit_map).1 y) (hx : x ∈ Z) : y ∈ Z :=
begin
  rw [profinite_limit_map_elem x, profinite_limit_map_elem y] at hxy,
  by_cases (Zᶜ).nonempty,
  { have I := profinite_limit_map.obj hZ (nonempty_of_mem hx) h,
    have hXY : (X_to_partition_map I x).1 = (X_to_partition_map I y).1,
    { change ((profinite_limit.image_elem x).1 I).1 = ((profinite_limit.image_elem y).1 I).1,
      rw hxy },
    rw X_to_partition_map_unique I x Z _ hx at hXY,
    { rw hXY, exact X_to_partition_map_point_mem I y },
    sorry },
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h,
  rw h,
  exact mem_univ y,
end

/-- Injectivity of profinite_limit_map -/
lemma profinite_limit_map.injective (X : Profinite) : function.injective (profinite_limit_map X) :=
begin
  intros x y hxy,
  rw ←singleton_eq_singleton_iff,
  rw ←(totally_disconnected_space_iff_connected_component_singleton.1 X.is_totally_disconnected),
  rw connected_component_eq_Inter_clopen,
  rw ←(totally_disconnected_space_iff_connected_component_singleton.1 X.is_totally_disconnected),
  rw connected_component_eq_Inter_clopen,
  suffices : ∀ Z : set X.to_Top.α, is_clopen Z → (x ∈ Z ↔ y ∈ Z),
  { apply eq_of_subset_of_subset,
    -- TODO: symmetry??
    { apply subset_Inter,
      rintro ⟨Z, ⟨hZ, hyZ⟩⟩,
      exact Inter_subset (λ Z : {Z // is_clopen Z ∧ x ∈ Z}, ↑Z) ⟨Z, ⟨hZ, (this Z hZ).2 hyZ⟩⟩ },
    apply subset_Inter,
    rintro ⟨Z, ⟨hZ, hxZ⟩⟩,
    exact Inter_subset (λ Z : {Z // is_clopen Z ∧ y ∈ Z}, ↑Z) ⟨Z, ⟨hZ, (this Z hZ).1 hxZ⟩⟩ },
  intros Z hZ,
  refine ⟨λ hx, profinite_limit_map.mem hZ hxy hx, λ hy, profinite_limit_map.mem hZ hxy.symm hy⟩,
end















/-
TODO:
profinite_inter_map,

show section is directed

show "elements" of section are clopen, nonempty
-/
#check finite_of_finite_image

def profinite_inter_obj {X : Profinite} (I J : profinite_skeleton X) : set (set X.to_Top.α) :=
λ U, ∃ (V W : set X.to_Top.α), (V ∈ I.1) ∧ (W ∈ J.1) ∧ U = V ∩ W ∧ U.nonempty

def profinite_inter_obj_injection {X : Profinite} (I J : profinite_skeleton X) :
  (profinite_inter_obj I J) → (prod I J) :=
λ U,
{ fst := ⟨classical.some U.2, (classical.some_spec (classical.some_spec U.2)).1⟩,
  snd := ⟨classical.some (classical.some_spec U.2),
          (classical.some_spec (classical.some_spec U.2)).2.1⟩ }

lemma profinite_inter_obj_injection_eq {X : Profinite} {I J : profinite_skeleton X}
  (U : profinite_inter_obj I J) :
  ↑U = (profinite_inter_obj_injection I J U).1.1 ∩ (profinite_inter_obj_injection I J U).2.1 :=
(classical.some_spec (classical.some_spec U.2)).2.2.1

lemma profinite_inter_obj_injection.injective {X : Profinite} (I J : profinite_skeleton X) :
  function.injective (profinite_inter_obj_injection I J) :=
begin
  refine λ U V hUV, subtype.ext _,
  rw [profinite_inter_obj_injection_eq U, profinite_inter_obj_injection_eq V, hUV],
end









#check function.injective.inj_on
#check finite.prod
#check finite.of_fintype
#check fintype.of_injective

def profinite_inter_map {X : Profinite} (I J : profinite_skeleton X) : profinite_skeleton X :=
⟨profinite_inter_obj I J,
begin
  refine ⟨_,_,_,_⟩,
  { sorry },
  { intros U hU,
    refine ⟨_,(classical.some_spec (classical.some_spec hU)).2.2.2⟩,
    have H : U = (profinite_inter_obj_injection I J ⟨U, hU⟩).1.1 ∩
      (profinite_inter_obj_injection I J ⟨U, hU⟩).2.1 := profinite_inter_obj_injection_eq ⟨U, hU⟩,
    rw H,
    { apply is_open_inter,
      { apply (I.2.2.1 (profinite_inter_obj_injection I J ⟨U, hU⟩).1.1
          (profinite_inter_obj_injection I J ⟨U, hU⟩).1.2).1 },
      apply (J.2.2.1 (profinite_inter_obj_injection I J ⟨U, hU⟩).2.1
          (profinite_inter_obj_injection I J ⟨U, hU⟩).2.2).1 } },
  { apply eq_univ_of_subset _ (eq.refl univ),
    intros x hx, sorry },

  -- disgustin proof :'(
  intros U V hU hV hUV,
  have hUi : U = (profinite_inter_obj_injection I J ⟨U, hU⟩).1.1 ∩
      (profinite_inter_obj_injection I J ⟨U, hU⟩).2.1 := profinite_inter_obj_injection_eq ⟨U, hU⟩,
  have hVi : V = (profinite_inter_obj_injection I J ⟨V, hV⟩).1.1 ∩
      (profinite_inter_obj_injection I J ⟨V, hV⟩).2.1 := profinite_inter_obj_injection_eq ⟨V, hV⟩,
  rw [hUi, inter_assoc, hVi] at hUV,
  conv at hUV {congr, congr, skip, rw [inter_comm, inter_assoc]},
  rw ←inter_assoc at hUV,
  have hI : (profinite_inter_obj_injection I J ⟨U, hU⟩).1.1 =
    (profinite_inter_obj_injection I J ⟨V, hV⟩).1.1,
  { apply I.2.2.2.2 _ _ (profinite_inter_obj_injection I J ⟨U, hU⟩).1.2
      (profinite_inter_obj_injection I J ⟨V, hV⟩).1.2,
    apply nonempty.mono _ hUV,
    -- TODO: remove tidy
    tidy },
  have hJ : (profinite_inter_obj_injection I J ⟨U, hU⟩).2.1 =
    (profinite_inter_obj_injection I J ⟨V, hV⟩).2.1,
  { apply J.2.2.2.2 _ _ (profinite_inter_obj_injection I J ⟨U, hU⟩).2.2
      (profinite_inter_obj_injection I J ⟨V, hV⟩).2.2,
    apply nonempty.mono _ hUV,
    -- TODO: remove tidy
    tidy },
  rw [hUi, hVi, hI, hJ],

end⟩

def section_to_set {X : Profinite} (u : X.profinite_limit.to_Top) :
 Π (I : X.profinite_skeleton), set X.to_Top.α := λ I, (u.1 I).1

lemma limit_section_directed {X : Profinite} (u : X.profinite_limit.to_Top) :
  directed (⊇) (section_to_set u) :=
begin
  rw profinite_limit.α X at u,
  intros I J,
  refine ⟨profinite_inter_map I J,_,_⟩,
  { sorry, -- TODO: separate lemma about ≤
  }, sorry,
end

#check is_compact.nonempty_Inter_of_directed_nonempty_compact_closed

lemma profinite_limit_map.surjective (X : Profinite) :
  function.surjective (profinite_limit_map X) :=
begin
  intro u,
  rw [profinite_limit.α X] at u,
  have H : (⋂ (I : (X.profinite_skeleton)), section_to_set u I).nonempty,
  {
    -- TODO:
    have : nonempty ↥(X.profinite_skeleton), {sorry },

    apply @is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _ _ _ this (section_to_set u)
      (limit_section_directed u); intro I,
    { sorry },
    { sorry },
    sorry },
  cases H with x hx,
  use x,
  suffices : (X.profinite_limit_map).1 x = u,
  { sorry },
  rw profinite_limit_map_elem,
  refine subtype.ext (funext (λ I, _)),
  change X_to_partition_map I x = u.1 I,
  apply subtype.ext,
  apply X_to_partition_map_unique,
  { apply profinite_diagram_obj' },
  apply mem_of_subset_of_mem (Inter_subset _ _) hx,
end

--noncomputable def profinite_limit_iso (X : Profinite) : X ≅ profinite_limit X :=

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
