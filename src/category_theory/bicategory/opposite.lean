import category_theory.bicategory.pseudofunctor

open category_theory

universes w₁ w₂ v₁ v₂ u₁ u₂

open category_theory.bicategory opposite

namespace category_theory

section bicategory

variables {B : Type u₁} [bicategory.{w₁ v₁} B]

instance bicategory.opposite : bicategory.{w₁ v₁} Bᵒᵖ :=
{ hom := λ a b, (unop b ⟶ unop a),
  comp := λ _ _ _ f g, g ≫ f,
  id   := λ a, 𝟙 (a.unop),
  category_hom := λ a b, bicategory.category_hom (unop b) (unop a),
  whisker_left :=  λ _ _ _ f _ _ η, bicategory.whisker_right η f,
  whisker_right := λ _ _ _ _ _ η h, bicategory.whisker_left h η,
  associator := λ _ _ _ _ f g h, (α_ h g f).symm,
  associator_naturality_left' := by { intros, apply associator_inv_naturality_right },
  associator_naturality_middle' := by { intros, apply associator_inv_naturality_middle },
  associator_naturality_right' := by { intros, apply associator_inv_naturality_left },
  left_unitor := λ _ _ f, right_unitor f,
  left_unitor_naturality' := by { intros, apply right_unitor_naturality },
  right_unitor := λ _ _ f, left_unitor f,
  right_unitor_naturality' := by { intros, apply left_unitor_naturality },
  pentagon' := by { intros, apply pentagon_inv },
  triangle' := by { intros, dsimp, apply triangle_assoc_comp_right } }

instance : category_struct.{v₁} Bᵒᵖ := bicategory.to_category_struct

instance : quiver.{v₁+1} Bᵒᵖ := bicategory.to_category_struct.to_quiver

end bicategory

namespace pseudofunctor

section

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {C : Type u₂} [bicategory.{w₂ v₂} C]
(F : pseudofunctor B C)

@[simps]
protected def op : pseudofunctor Bᵒᵖ Cᵒᵖ :=
{ map₀ := λ a, op (F.map₀ (unop a)),
  map₁ := λ _ _ f, F.map₁ f,
  map₂ := λ _ _ _ _ η, F.map₂ η,
  map₁_id := λ a, F.map₁_id (unop a),
  map₁_comp := λ _ _ _ f g, F.map₁_comp g f,
  map₁_comp_naturality_left' := by
  { intros, erw map₁_comp_naturality_right, refl },
  map₁_comp_naturality_right' := by
  { intros, erw map₁_comp_naturality_left, refl },
  map₂_id' := by { intros, erw map₂_id },
  map₂_comp' := by { intros, erw map₂_comp },
  map₂_associator' := by { intros, erw map₂_associator_inv, refl },
  map₂_left_unitor' := by { intros, erw map₂_right_unitor, refl },
  map₂_right_unitor' := by { intros, erw map₂_left_unitor, refl } }

end

end pseudofunctor

end category_theory
