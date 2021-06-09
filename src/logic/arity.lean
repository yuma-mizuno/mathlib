import data.fin

universes u v w

/-- The type of `n + 1`-ary functions `α → α → ... → α`. -/
def ary_fun (α : Type u) (β : Type v) : ℕ → Type (max u v)
| 0     := α → β
| (n+1) := α → ary_fun n

/-- The type of `n + 1`-ary relations `α → α → ... → Prop`. -/
def ary_rel (α : Type u) := ary_fun α Prop

variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type*} {n : ℕ}

namespace ary_fun

/-- Constant `n + 1`-ary function with value `b`. -/
def const (b : β) : ∀ n, ary_fun α β n
| 0 := λ _, b
| (n+1) := λ _, const n

instance ary_fun.inhabited [inhabited β] : inhabited (ary_fun α β n) :=
⟨const (default _) _⟩

/-- Precompose an `n + 1`-ary function with another function. -/
def precompose : Π {n : ℕ}, ary_fun β γ n → (α → β) → ary_fun α γ n
| 0 f g := f ∘ g
| (n + 1) f g := λ a, precompose (f (g a)) g

/-- Postcompose an `n + 1`-ary function with another function. -/
def postcompose : Π {n : ℕ}, ary_fun α β n → (β → γ) → ary_fun α γ n
| 0 f g := g ∘ f
| (n + 1) f g := λ a, postcompose (f a) g

@[simp] lemma precompose_zero {f : ary_fun β γ 0} {g : α → β} :
  f.precompose g = f ∘ g := rfl

@[simp] lemma precompose_succ {f : ary_fun β γ (n + 1)} {g : α → β} {a : α} :
  f.precompose g a = (f (g a)).precompose g := rfl

@[simp] lemma precompose_id {f : ary_fun α β n} :
  f.precompose id = f :=
begin
  induction n with n ih,
  { simp },
  { ext,
    simp [ih] }
end

lemma precompose_comp {f : ary_fun γ δ n} {g : α → β} {h : β → γ} :
  f.precompose (h ∘ g) = (f.precompose h).precompose g :=
begin
  induction n with n ih,
  { simp },
  { ext,
    simp [ih] }
end

@[simp] lemma postcompose_zero {f : ary_fun α β 0} {g : β → γ} :
  f.postcompose g = g ∘ f := rfl

@[simp] lemma postcompose_succ {f : ary_fun α β (n + 1)} {g : β → γ} {a : α} :
  f.postcompose g a = (f a).postcompose g := rfl

@[simp] lemma postcompose_id {f : ary_fun α β n} :
  f.postcompose id = f :=
begin
  induction n with n ih,
  { simp },
  { ext,
    simp [ih] }
end

lemma postcompose_comp {f : ary_fun α β n} {g : β → γ} {h : γ → δ} :
  f.postcompose (h ∘ g) = (f.postcompose g).postcompose h :=
begin
  induction n with n ih,
  { simp },
  { ext,
    simp [ih] }
end

/-- An `n + 1`-ary function as a function on tuples. -/
def fin_map : Π {n}, ary_fun α β n → (fin (n + 1) → α) → β
| 0 f x := f (x 0)
| (n + 1) f x := (f (x 0)).fin_map (fin.tail x)

@[simp] lemma fin_map_zero_apply {f : ary_fun α β 0} {x : fin 1 → α} :
  f.fin_map x = f (x 0) := rfl

@[simp] lemma fin_map_succ_apply {f : ary_fun α β (n + 1)} {x : fin (n + 2) → α} :
  f.fin_map x = (f (x 0)).fin_map (fin.tail x) := rfl

@[simp] lemma precompose_fin_map_apply {f : ary_fun β γ n} {g : α → β} {x : fin (n + 1) → α} :
  (f.precompose g).fin_map x = f.fin_map (g ∘ x) :=
begin
  induction n with n ih,
  { refl },
  simp [ih, fin.comp_tail],
end

@[simp] lemma postcompose_fin_map {f : ary_fun α β n} {g : β → γ} :
  (f.postcompose g).fin_map = g ∘ f.fin_map :=
begin
  ext x,
  induction n with n ih,
  { refl },
  simp [ih],
end

/-- A function on tuples, cast as an `n + 1`-ary function. -/
def of_fin_map : Π {n}, ((fin (n + 1) → α) → β) → ary_fun α β n
| 0 f := λ a, f (λ _, a)
| (n + 1) f := λ a, of_fin_map (λ x, f (fin.cons a x))

@[simp] lemma of_fin_map_zero_apply {f : (fin 1 → α) → β} {a : α} :
  of_fin_map f a = f (λ _, a) := rfl

@[simp] lemma of_fin_map_succ_apply {f : (fin (n + 2) → α) → β} {a : α} :
  (of_fin_map f) a = of_fin_map (λ x, f (fin.cons a x)) := rfl

/-- The equivalence between `n + 1`-ary functions and functions on tuples. -/
def equiv_fin_map : ary_fun α β n ≃ ((fin (n + 1) → α) → β) :=
⟨fin_map, of_fin_map, λ f, begin
  induction n with n ih,
  { refl },
  ext a,
  simp only [of_fin_map, fin_map, fin.cons_zero, fin.tail_cons, ih],
end, λ f, begin
  induction n with n ih,
  { ext x,
    simp only [of_fin_map, fin_map],
    exact congr rfl (funext (λ a, congr rfl (subsingleton.elim _ _))), },
  { ext x,
    simp [of_fin_map, fin_map, ih] }
end⟩

@[simp] lemma coe_equiv_fin_map :
  (equiv_fin_map : ary_fun α β n → ((fin (n + 1) → α) → β)) = fin_map := rfl

@[simp] lemma coe_symm_equiv_fin_map :
  (equiv_fin_map.symm : ((fin (n + 1) → α) → β) → ary_fun α β n) = of_fin_map := rfl

lemma fin_map_ext_iff {f g : ary_fun α β n} :
  f = g ↔ ∀ (x : fin (n + 1) → α), f.fin_map x = g.fin_map x :=
begin
  split,
  { rintro rfl,
    exact λ _, rfl },
  { intro h,
    apply equiv_fin_map.injective,
    ext x,
    simp [h] }
end

lemma precompose_postcompose {f : ary_fun β γ n} {g : α → β} {h : γ → δ} :
  (f.precompose g).postcompose h = (f.postcompose h).precompose g :=
begin
  rw fin_map_ext_iff,
  intro x,
  simp,
end

end ary_fun

namespace ary_rel

/-- The implication relation on `n + 1`-ary relations, which forms a partial order. -/
def implies : Π {n : ℕ}, (ary_rel α n) → (ary_rel α n) → Prop
| 0 r s := ∀ a, r a → s a
| (n + 1) r s := ∀ a, implies (r a) (s a)

instance {n : ℕ} : partial_order (ary_rel α n) :=
{ le := implies,
  le_refl := λ r, begin
    induction n with n ih,
    { exact λ _, id },
    { exact λ _, ih _ }
  end,
  le_antisymm := λ r s, begin
    induction n with n ih,
    { exact λ rs sr, funext (λ a, iff_iff_eq.1 ⟨rs a, sr a⟩), },
    { exact λ rs sr, funext (λ a, ih _ _ (rs a) (sr a)), }
  end,
  le_trans := λ r s t, begin
    induction n with n ih,
    { exact λ rs st a ra, st a (rs a ra) },
    { exact λ rs st a, ih (r a) (s a) (t a) (rs a) (st a) }
  end }

lemma le_iff_fin_map_implies_fin_map {r s : ary_rel α n} :
  r ≤ s ↔ ∀ x, r.fin_map x → s.fin_map x :=
begin
  split,
  { intros rs x rx,
    induction n with n ih,
    { exact rs (x 0) rx },
    exact ih (rs (x 0)) _ rx },
  { induction n with n ih,
    { exact λ h a, h (λ _, a) },
    { refine λ h a, ih (λ x rx, _),
      have h' := h (fin.cons a x),
      simp only [ary_fun.fin_map_succ_apply, fin.cons_zero, fin.tail_cons] at h',
      exact h' rx } }
end

lemma precompose_mono {r s : ary_rel β n} {f : α → β} (h : r ≤ s) :
  ((≤) : ary_rel α n → ary_rel α n → Prop) (r.precompose f) (s.precompose f) :=
begin
  rw le_iff_fin_map_implies_fin_map at *,
  intros x rx,
  rw [ary_fun.precompose_fin_map_apply] at *,
  exact h _ rx,
end

end ary_rel
