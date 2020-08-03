import model_theory.basic
import model_theory.arity

open nat set

universes u v

local notation h :: t  := fin.cons h t
local notation `[` l:(foldr `, ` (h t, fin.cons h t) fin.elim0 `]`:0) := l



variable (L : Language.{u})

namespace fol

/- preterm L l is a partially applied term. if applied to n terms, it becomes a term.
* Every element of preterm L 0 is a well-formed term.
* We use this encoding to avoid mutual or nested inductive types, since those are not too convenient to work with in Lean. -/
inductive preterm : ℕ → Type u
| var {} : ∀ (k : ℕ), preterm 0
| func : ∀ {l : ℕ} (f : L.functions l), preterm l
| app : ∀ {l : ℕ} (t : preterm (l + 1)) (s : preterm 0), preterm l
export preterm

@[reducible] def term := preterm L 0

variable {L}
prefix `&`:max := fol.preterm.var

@[simp] def apps : ∀{l}, preterm L l → (fin l → (term L)) → term L
| 0 t _     := t
| (l+1) t ts := apps (app t (ts 0)) (fin.tail ts)

@[simp] lemma apps_zero (t : term L) (ts : fin 0 → term L) : apps t ts = t := rfl

lemma apps_eq_app {l} (t : preterm L (l+1)) (s : term L) (ts : fin l → term L) :
  ∃t' s', apps t (s :: ts) = app t' s' :=
begin
  --induction ts generalizing s, exact ⟨t, s, rfl⟩, exact ts_ih (app t s) ts_x
  revert s, induction l, simp, intro s,
  have h := l_ih (app t s) (fin.tail ts) (ts 0), simp at *,
  cases h with t' ht', cases ht' with s' h, use [t',s'], rw ← h,
end

namespace preterm
@[simp] def change_arity' : ∀{l l'} (h : l = l') (t : preterm L l), preterm L l'
| _ _ h &k          := by induction h; exact &k
| _ _ h (func f)    := func (by induction h; exact f)
| _ _ h (app t₁ t₂) := app (change_arity' (congr_arg nat.succ h) t₁) t₂

@[simp] lemma change_arity'_rfl : ∀{l} (t : preterm L l), change_arity' rfl t = t
| _ &k          := by refl
| _ (func f)    := by refl
| _ (app t₁ t₂) := by dsimp; simp*

end preterm

lemma apps_ne_var {l} {f : L.functions l} {ts : fin l → term L} {k : ℕ} :
  apps (func f) ts ≠ &k :=
begin
  intro h, cases l, injection h,
  rcases apps_eq_app (func f) (ts 0) (fin.tail ts) with ⟨t, s, h'⟩,
  simp only [fin.cons_self_tail] at h',
  cases h.symm.trans h',
end

lemma apps_inj' {l} {t t' : preterm L l} {ts ts' : fin l → term L}
  (h : apps t ts = apps t' ts') : t = t' ∧ ts = ts' :=
begin
  induction l,
  {  dsimp at h, exact ⟨h, subsingleton.elim _ _⟩, },
  { dsimp at h, have h1 := l_ih h,
    simp only [] at h1, split, apply h1.left.left,
    rw [← fin.cons_self_tail ts, ← fin.cons_self_tail ts', h1.right, h1.left.right], }
end

lemma apps_inj {l} {f f' : L.functions l} {ts ts' : fin l → term L}
  (h : apps (func f) ts = apps (func f') ts') : f = f' ∧ ts = ts' :=
by rcases apps_inj' h with ⟨h', rfl⟩; cases h'; exact ⟨rfl, rfl⟩


/- preformula l is a partially applied formula. if applied to n terms, it becomes a formula.
  * We only have implication as binary connective. Since we use classical logic, we can define
    the other connectives from implication and falsum.
  * Similarly, universal quantification is our only quantifier.
  * We could make `falsum` and `equal` into elements of rel. However, if we do that, then we cannot make the interpretation of them in a model definitionally what we want.
-/
variable (L)
inductive preformula : ℕ → Type u
| falsum {} : preformula 0
| equal (t₁ t₂ : term L) : preformula 0
| rel {l : ℕ} (R : L.relations l) : preformula l
| apprel {l : ℕ} (f : preformula (l + 1)) (t : term L) : preformula l
| imp (f₁ f₂ : preformula 0) : preformula 0
| all (f : preformula 0) : preformula 0
export preformula
@[reducible] def formula := preformula L 0
variable {L}

notation `⊥` := fol.preformula.falsum -- input: \bot
infix ` ≃ `:88 := fol.preformula.equal -- input \~- or \simeq
infixr ` ⟹ `:62 := fol.preformula.imp -- input \==>
prefix `∀'`:110 := fol.preformula.all
def not   (f : formula L)     : formula L := f ⟹ ⊥
prefix `∼`:max := fol.not -- input \~, the ASCII character ~ has too low precedence
notation `⊤` := ∼⊥ -- input: \top
def and   (f₁ f₂ : formula L) : formula L := ∼(f₁ ⟹ ∼f₂)
infixr ` ⊓ ` := fol.and -- input: \sqcap
def or    (f₁ f₂ : formula L) : formula L := ∼f₁ ⟹ f₂
infixr ` ⊔ ` := fol.or -- input: \sqcup
def biimp (f₁ f₂ : formula L) : formula L := (f₁ ⟹ f₂) ⊓ (f₂ ⟹ f₁)
infix ` ⇔ `:61 := fol.biimp -- input \<=>
def ex    (f : formula L)     : formula L := ∼ ∀' ∼f
prefix `∃'`:110 := fol.ex -- input \ex

@[simp] def apps_rel : ∀{l} (f : preformula L l) (ts : fin l → term L), formula L
| 0     f  _      := f
| (n+1) f x := apps_rel (apprel f (x 0)) (fin.tail x)

@[simp] lemma apps_rel_zero (f : formula L) (ts : fin 0 → term L) : apps_rel f ts = f := rfl

@[simp] lemma apps_rel_cons {l : ℕ} (f : preformula L (l + 1)) (t : term L) (ts : fin l → term L) :
  apps_rel f (t :: ts) = apps_rel (apprel f t) ts := by simp

def formula_of_relation {l} (R : L.relations l) : arity' (term L) (formula L) l :=
arity'.of_dvector_map $ apps_rel (rel R)

@[elab_as_eliminator] def formula.rec' {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : fin l → term L), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f)) :
  ∀{l} (f : preformula L l) (ts : fin l → term L), C (apps_rel f ts)
| _ falsum       ts := hfalsum
| _ (t₁ ≃ t₂)    ts := by apply hequal
| _ (rel R)      ts := by apply hrel
| _ (apprel f t) ts := eq.mp (by simp) (formula.rec' f (t :: ts))
| _ (f₁ ⟹ f₂)   ts := himp (formula.rec' f₁ ([])) (formula.rec' f₂ ([]))
| _ (∀' f)       ts := hall (formula.rec' f ([]))

@[elab_as_eliminator] def formula.rec {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : fin l → term L), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f)) : ∀f, C f :=
λf, formula.rec' hfalsum hequal hrel himp hall f ([])

@[simp] def formula.rec'_apps_rel {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : fin l → term L), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f))
  {l} (f : preformula L l) (ts : fin l → term L) :
  @formula.rec' L C hfalsum hequal hrel himp hall 0 (apps_rel f ts) ([]) =
  @formula.rec' L C hfalsum hequal hrel himp hall l f ts :=
begin
  induction l,
  { congr, exact subsingleton.elim _ _, },
  { rw ← fin.cons_self_tail ts, dsimp only [apps_rel], rw [l_ih], unfold formula.rec', sorry }
end

@[simp] def formula.rec_apps_rel {C : formula L → Sort v}
  (hfalsum : C ⊥)
  (hequal : Π (t₁ t₂ : term L), C (t₁ ≃ t₂))
  (hrel : Π {{l}} (R : L.relations l) (ts : fin l → term L), C (apps_rel (rel R) ts))
  (himp : Π {{f₁ f₂ : formula L}} (ih₁ : C f₁) (ih₂ : C f₂), C (f₁ ⟹ f₂))
  (hall : Π {{f : formula L}} (ih : C f), C (∀' f))
  {l} (R : L.relations l) (ts : fin l → term L) :
  @formula.rec L C hfalsum hequal hrel himp hall (apps_rel (rel R) ts) = hrel R ts :=
by dsimp only [formula.rec]; rw formula.rec'_apps_rel; refl


end fol
