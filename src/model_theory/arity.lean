import data.fin

universe u

/-- The type α → (α → ... (α → β)...) with n α's. We require that α and β live in the same universe, otherwise we have to use ulift. -/
def arity' (α β : Type u) : ℕ → Type u
| 0     := β
| (n+1) := α → arity' n

namespace arity'
section arity'

def fin.nil {α : Type u} : fin 0 → α := default _

local notation h :: t  := fin.cons h t
local notation `[` l:(foldr `, ` (h t,fin.cons h t) fin.nil `]`) := l

def arity'_constant {α β : Type u} : ∀{n : ℕ}, β → arity' α β n
| 0     b := b
| (n+1) b := λ_, arity'_constant b

@[simp] def of_dvector_map {α β : Type u} : ∀{l} (f : (fin l → α) → β), arity' α β l
| 0     f := f ([])
| (l+1) f := λx, of_dvector_map $ λxs, f $ x::xs

@[simp] def arity'_app {α β : Type u} : ∀{l}, arity' α β l → (fin l → α) → β
| 0 b _      := b
| (l + 1) f x := arity'_app (f (x 0)) (fin.tail x)

@[simp] lemma arity'_app_zero {α β : Type u} (f : arity' α β 0) (xs : fin 0 → α) :
  arity'_app f xs = f :=
by cases xs; refl

def arity'_postcompose {α β γ : Type u} (g : β → γ) : ∀{n} (f : arity' α β n), arity' α γ n
| 0     b := g b
| (n+1) f := λx, arity'_postcompose (f x)

def arity'_postcompose2 {α β γ δ : Type u} (h : β → γ → δ) :
  ∀{n} (f : arity' α β n) (g : arity' α γ n), arity' α δ n
| 0     b c := h b c
| (n+1) f g := λx, arity'_postcompose2 (f x) (g x)

def arity'_precompose {α β γ : Type u} : ∀{n} (g : arity' β γ n) (f : α → β), arity' α γ n
| 0     c f := c
| (n+1) g f := λx, arity'_precompose (g (f x)) f

inductive arity'_respect_setoid {α β : Type u} [R : setoid α] : ∀{n}, arity' α β n → Type u
| r_zero (b : β) : @arity'_respect_setoid 0 b
| r_succ (n : ℕ) (f : arity' α β (n+1)) (h₁ : ∀{{a a'}}, a ≈ a' → f a = f a')
  (h₂ : ∀a, arity'_respect_setoid (f a)) : arity'_respect_setoid f
open arity'_respect_setoid

instance subsingleton_arity'_respect_setoid {α β : Type u} [R : setoid α] {n} (f : arity' α β n) :
  subsingleton (arity'_respect_setoid f) :=
begin
  constructor, intros h h', induction h generalizing h'; cases h'; try {refl}; congr,
  apply funext, intro x, apply h_ih
end

-- def arity'_quotient_lift {α β : Type u} {R : setoid α} :
--   ∀{n}, (Σ(f : arity' α β n), arity'_respect_setoid f) → arity' (quotient R) β n
-- | _ ⟨_, r_zero b⟩         := b
-- | _ ⟨_, r_succ n f h₁ h₂⟩ :=
--   begin
--     apply quotient.lift (λx, arity'_quotient_lift ⟨f x, h₂ x⟩),
--     intros x x' r, dsimp,
--     apply congr_arg, exact sigma.eq (h₁ r) (subsingleton.elim _ _)
--   end

-- def arity'_quotient_beta {α β : Type u} {R : setoid α} {n} (f : arity' α β n)
--   (hf : arity'_respect_setoid f) (xs : dvector α n) :
--   arity'_app (arity'_quotient_lift ⟨f, hf⟩) (xs.map quotient.mk) = arity'_app f xs :=
-- begin
--   induction hf,
--   { simp [arity'_quotient_lift] },
--   dsimp [arity'_app], sorry
-- end

def for_all {α : Type u} (P : α → Prop) : Prop := ∀x, P x

@[simp] def arity'_map2 {α β : Type u} (q : (α → β) → β) (f : β → β → β) :
  ∀{n}, arity' α β n → arity' α β n → β
| 0     x y := f x y
| (n+1) x y := q (λz, arity'_map2 (x z) (y z))

@[simp] lemma arity'_map2_refl {α : Type} {f : Prop → Prop → Prop} (r : ∀A, f A A) :
  ∀{n} (x : arity' α Prop n), arity'_map2 for_all f x x
| 0     x := r x
| (n+1) x := λy, arity'_map2_refl (x y)

def arity'_imp {α : Type} {n : ℕ} (f₁ f₂ : arity' α Prop n) : Prop :=
arity'_map2 for_all (λP Q, P → Q) f₁ f₂

def arity'_iff {α : Type} {n : ℕ} (f₁ f₂ : arity' α Prop n) : Prop :=
arity'_map2 for_all iff f₁ f₂

lemma arity'_iff_refl {α : Type} {n : ℕ} (f : arity' α Prop n) : arity'_iff f f :=
arity'_map2_refl iff.refl f

lemma arity'_iff_rfl {α : Type} {n : ℕ} {f : arity' α Prop n} : arity'_iff f f :=
arity'_iff_refl f

end arity'
end arity'
