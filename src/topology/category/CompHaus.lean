/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import topology.category.Top

/-!

# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/

open category_theory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_hausdorff : t2_space to_Top]

namespace CompHaus

instance : inhabited CompHaus := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort CompHaus := ⟨Type*, λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : category CompHaus := induced_category.category to_Top

@[simp]
lemma coe_to_Top {X : CompHaus} : (X.to_Top : Type*) = X :=
rfl

end  CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps {rhs_md := semireducible}, derive [full, faithful]]
def CompHaus_to_Top : CompHaus ⥤ Top := induced_functor _

namespace Top

open category_theory.limits

lemma limit_compact (J : Type*)
  (𝒥 : small_category J)
  (F : J ⥤ Top)
  [∀ j, compact_space (F.obj j)] :
  compact_space (Top.limit_cone F).X :=
begin
  set f : (Top.limit_cone F).X → Π (j : J), F.obj j := λ x, x.val with hf,
  have hfc : continuous f,
    sorry,
  sorry
end

lemma limit_t2 (J : Type*)
  (𝒥 : small_category J)
  (F : J ⥤ Top)
  [∀ j, t2_space (F.obj j)] :
  t2_space (Top.limit_cone F).X :=
begin
  set f : (Top.limit_cone F).X → Π (j : J), F.obj j := λ x, x.val with hf,
  have hfc : continuous f,
    sorry,
  sorry
end

end Top

namespace CompHaus

open Top

def limit_aux (J : Type*)
  (𝒥 : small_category J)
  (F : J ⥤ CompHaus) :
  CompHaus :=
{ to_Top := (limit_cone (F ⋙ CompHaus_to_Top)).X,
  is_compact := @limit_compact J 𝒥 (F ⋙ CompHaus_to_Top) (λ j, (F.obj j).is_compact),
  is_hausdorff := @limit_t2 J 𝒥 (F ⋙ CompHaus_to_Top) (λ j, (F.obj j).is_hausdorff)}

end CompHaus
