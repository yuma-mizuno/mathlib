/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import topology.category.CompHaus
import category_theory.limits.shapes.products

/-!
# The category of Profinite Types
We construct the category of profinite topological spaces,
often called profinite sets -- perhaps they could be called
profinite types in Lean.

The type of profinite topological spaces is called `Profinite`. It has a category
instance and is a fully faithful subcategory of `Top`. The fully faithful functor
is called `Profinite_to_Top`.

-- TODO
1) existence of products, limits(?), finite coproducts
2) `Profinite_to_Top` creates limits?
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

end Profinite

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def Profinite_to_Top : Profinite ⥤ Top := induced_functor _

/-- The fully faithful embedding of `Profinite` in `Top`. -/
@[simps] def Profinite_to_CompHaus : Profinite ⥤ CompHaus :=
{ obj := λ X, { to_Top := X.to_Top,
  is_compact := X.is_compact,
  is_hausdorff := X.is_t2 },
  map := λ _ _ f, f }

instance : full Profinite_to_CompHaus := { preimage := λ _ _ f, f }
instance : faithful Profinite_to_CompHaus := {}

@[simp] lemma Profinite_to_CompHaus_to_Top :
  Profinite_to_CompHaus ⋙ CompHaus_to_Top = Profinite_to_Top :=
rfl

#check limits.is_limit.of_faithful

namespace Profinite

open category_theory.limits

--def limit_aux
#check continuous_apply
-- λp:Πi, π i, p i
variable {J : Type*}
#check Top.limit_cone


def product_cone (F : (discrete J) ⥤ Profinite) : cone F :=
{
  X := { to_Top := { α := Π (i : J), (F.obj i)},
        is_compact := by apply_instance,
        is_t2 := Pi.t2_space,
        is_totally_disconnected :=
        {
        is_totally_disconnected_univ :=
        begin
          intros t sub_t preconn_t, constructor,
          intros a b, ext,
          have H1 : subsingleton ((λ c : (Π (i : J), (F.obj i)), c x )'' t),
            {
              cases (F.obj x).is_totally_disconnected with H,
              apply H, simp,
              apply is_preconnected.image, exact preconn_t,
              apply continuous.continuous_on,
              apply continuous_apply,
            },
          cases H1,
          have H2 := H1 ⟨(a.1 x), by {simp, use a, split, simp}⟩,
          have H3 := H2 ⟨(b.1 x), by {simp, use b, split, simp}⟩,
          simp at H3, exact H3,
        end
        }
      },
  π := { app := λ i : J, ⟨λ p : (Π (j : J), F.obj j), p i, continuous_apply _⟩},
}

def product_cone_is_limit (F : (discrete J) ⥤ Profinite) : is_limit (product_cone F) :=
{
  lift := λ s, ⟨λ (x : s.X), (λ (i : J), (s.π.app i) x), continuous_pi (λ i, (s.π.app i).2)⟩,
  uniq' := by {intros, ext x j, apply (congr_fun (congr_arg (@continuous_map.to_fun s.X ( F.obj j) _ _) (w j)) x)},
}

instance Profinite_has_products : has_products Profinite :=
λ J, { has_limit := λ F, has_limit.mk { cone := product_cone F, is_limit := product_cone_is_limit F } }

end Profinite
