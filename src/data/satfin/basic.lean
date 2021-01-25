import data.nat.cast
import order.bounded_lattice
import data.fintype.basic

lemma nat.le_of_add_le_left {k l m : ℕ} (h : k + l ≤ m) : k ≤ m :=
by { refine le_trans _ h, simp }

lemma nat.le_of_add_le_right {k l m : ℕ} (h : k + l ≤ m) : l ≤ m :=
by { refine le_trans _ h, simp }

open nat function

/-- `satfin n` is the subtype of `ℕ` consisting of natural numbers strictly smaller than `n`. -/
def satfin (n : ℕ) := {i : ℕ // i < n}

namespace satfin

section core_basic

/-- Backwards-compatible constructor for `satfin n`. -/
def mk {n : ℕ} (i) (h) : satfin n := ⟨i, h⟩

instance satfin_to_nat (n : ℕ) : has_coe (satfin n) nat := ⟨subtype.val⟩

protected def lt {n} (a b : satfin n) : Prop :=
(a : ℕ) < b

protected def le {n} (a b : satfin n) : Prop :=
(a : ℕ) ≤ b

instance {n} : has_lt (satfin n)  := ⟨satfin.lt⟩
instance {n} : has_le (satfin n)  := ⟨satfin.le⟩

instance decidable_lt {n} (a b : satfin n) :  decidable (a < b) :=
nat.decidable_lt _ _

instance decidable_le {n} (a b : satfin n) : decidable (a ≤ b) :=
nat.decidable_le _ _

def {u} elim0 {α : satfin 0 → Sort u} : Π (x : satfin 0), α x
| ⟨_, h⟩ := absurd h (not_lt_zero _)

variable {n : ℕ}

lemma eq_of_veq : ∀ {i j : satfin n}, (i : ℕ) = j → i = j
| ⟨iv, ilt₁⟩ ⟨.(iv), ilt₂⟩ rfl := rfl

lemma veq_of_eq : ∀ {i j : satfin n}, i = j → (i : ℕ) = j
| ⟨iv, ilt⟩ .(_) rfl := rfl

lemma ne_of_vne {i j : satfin n} (h : (i : ℕ) ≠ j) : i ≠ j :=
λ h', absurd (veq_of_eq h') h

lemma vne_of_ne {i j : satfin n} (h : i ≠ j) : (i : ℕ) ≠ j :=
λ h', absurd (eq_of_veq h') h

open satfin

instance (n : ℕ) : decidable_eq (satfin n) :=
λ i j, decidable_of_decidable_of_iff
  (nat.decidable_eq i j) ⟨eq_of_veq, veq_of_eq⟩

end core_basic

section core_addt

open satfin

variable {n : ℕ}

/-- Elimination principle for the empty set `satfin 0`, dependent version. -/
def {u} satfin_zero_elim {α : satfin 0 → Sort u} (x : satfin 0) : α x := x.elim0

lemma lt_iff_vlt {n} {a b : satfin n} : a < b ↔ (a : ℕ) < b := iff.rfl
lemma le_iff_vle {n} {a b : satfin n} : a ≤ b ↔ (a : ℕ) ≤ b := iff.rfl

lemma eq_iff_veq {i j : satfin n} : i = j ↔ (i : ℕ) = j :=
⟨veq_of_eq, eq_of_veq⟩

lemma ne_iff_vne {i j : satfin n} : i ≠ j ↔ (i : ℕ) ≠ j :=
⟨vne_of_ne, ne_of_vne⟩

end core_addt

section basic

open satfin

variables {n m : ℕ} {a b : satfin n}

section coe

@[simp] protected lemma eta (a : satfin n) (h : (a : ℕ) < n) : (⟨(a : ℕ), h⟩ : satfin n) = a :=
by cases a; refl

@[ext] lemma ext (h : (a : ℕ) = b) : a = b := eq_of_veq h

lemma ext_iff (a b : satfin n) : a = b ↔ (a : ℕ) = b := eq_iff_veq

lemma coe_injective {n : ℕ} : injective (coe : satfin n → ℕ) := subtype.coe_injective

@[simp] lemma mk_eq_subtype_mk (a : ℕ) (h : a < n) : mk a h = ⟨a, h⟩ := rfl

protected lemma mk.inj_iff {a b : ℕ} {ha : a < n} {hb : b < n} :
  (⟨a, ha⟩ : satfin n) = ⟨b, hb⟩ ↔ a = b :=
subtype.mk_eq_mk

lemma mk_val (h : n < m) : (⟨n, h⟩ : satfin m).val = n := rfl

lemma eq_mk_iff_coe_eq {k : ℕ} {hk : k < n} : a = ⟨k, hk⟩ ↔ (a : ℕ) = k :=
eq_iff_veq

@[simp, norm_cast] lemma coe_mk {m n : ℕ} (h : m < n) : ((⟨m, h⟩ : satfin n) : ℕ) = m := rfl

lemma mk_coe (i : satfin n) : (⟨i, i.property⟩ : satfin n) = i :=
satfin.eta _ _

lemma coe_eq_val (a : satfin n) : (a : ℕ) = a.val := rfl

@[simp] lemma val_eq_coe (a : satfin n) : a.val = a := rfl

/-- Assume `n = m`. If two functions defined on `fin n` and `fin m` are equal on each element,
then they coincide (in the heq sense). -/
protected lemma heq_fun_iff {α : Type*} (h : n = m) {f : satfin n → α} {g : satfin m → α} :
  f == g ↔ (∀ (i : satfin n), f i = g ⟨(i : ℕ), h ▸ i.2⟩) :=
by { induction h, simp [heq_iff_eq, function.funext_iff] }

protected lemma heq_ext_iff (h : n = m) {i j : satfin n} :
  i == j ↔ (i : ℕ) = (j : ℕ) :=
by { induction h, simp [ext_iff] }

lemma exists_iff {p : satfin n → Prop} : (∃ i, p i) ↔ ∃ i h, p ⟨i, h⟩ :=
⟨λ h, exists.elim h (λ ⟨i, hi⟩ hpi, ⟨i, hi, hpi⟩),
  λ h, exists.elim h (λ i hi, ⟨⟨i, hi.fst⟩, hi.snd⟩)⟩

lemma forall_iff {p : satfin n → Prop} : (∀ i, p i) ↔ ∀ i h, p ⟨i, h⟩ :=
⟨λ h i hi, h ⟨i, hi⟩, λ h ⟨i, hi⟩, h i hi⟩

end coe

section order

lemma is_lt (i : satfin n) : (i : ℕ) < n := i.property

lemma is_le (i : satfin (n + 1)) : (i : ℕ) ≤ n := le_of_lt_succ i.is_lt

/-- `a < b` as natural numbers if and only if `a < b` in `satfin n`. -/
@[norm_cast, simp] lemma coe_fin_lt : (a : ℕ) < (b : ℕ) ↔ a < b :=
iff.rfl

/-- `a ≤ b` as natural numbers if and only if `a ≤ b` in `satfin n`. -/
@[norm_cast, simp] lemma coe_fin_le : (a : ℕ) ≤ (b : ℕ) ↔ a ≤ b :=
iff.rfl

lemma mk_lt_of_lt_coe {a : ℕ} (h : a < b) : (⟨a, h.trans b.is_lt⟩ : satfin n) < b := h

lemma mk_le_of_le_coe {a : ℕ} (h : a ≤ b) : (⟨a, h.trans_lt b.is_lt⟩ : satfin n) ≤ b := h

instance : linear_order (satfin n) :=
{ le := (≤), lt := (<),
  decidable_le := satfin.decidable_le,
  decidable_lt := satfin.decidable_lt,
  decidable_eq := satfin.decidable_eq _,
 ..linear_order.lift (coe : satfin n → ℕ) (@satfin.eq_of_veq _) }

instance : has_zero (satfin (n + 1)) := ⟨⟨0, succ_pos n⟩⟩

@[simp] lemma coe_zero : ((0 : satfin (n + 1)) : ℕ) = 0 := rfl
lemma val_zero : (0 : satfin (n + 1)).val = 0 := rfl
@[simp] lemma mk_zero : (⟨0, succ_pos'⟩ : satfin (n + 1)) = (0 : satfin _) := rfl

lemma zero_le (a : satfin (n + 1)) : 0 ≤ a := zero_le a

instance : inhabited (satfin (n + 1)) := ⟨0⟩

instance subsingleton_zero : subsingleton (satfin 0) := ⟨satfin.elim0⟩
instance subsingleton_one : subsingleton (satfin 1) := ⟨begin
    rintro ⟨_|a, ha⟩ ⟨_|b, hb⟩,
    { refl },
    all_goals { exact absurd ‹succ _ < 1› (not_lt_of_le (le_of_inf_eq rfl)) } end⟩

/-- The greatest value of `satfin (n+1)` -/
def last (n : ℕ) : satfin (n + 1) := ⟨_, n.lt_succ_self⟩

@[simp, norm_cast] lemma coe_last (n : ℕ) : (last n : ℕ) = n := rfl

lemma last_val (n : ℕ) : (last n).val = n := rfl

lemma le_last (i : satfin (n + 1)) : i ≤ last n :=
le_of_lt_succ i.is_lt

instance : bounded_lattice (satfin (n + 1)) :=
{ top := last n,
  le_top := le_last,
  bot := 0,
  bot_le := zero_le,
  .. satfin.linear_order, .. lattice_of_linear_order }

instance : fintype (satfin n) :=
{ elems := finset.subtype (λ x, x < n) (finset.range n),
  complete := λ ⟨x, h⟩, by simp [h] }

end order

section add

-- We use a saturating addition, which can correspond to a tropical semiring structure
-- with `(min, +)` as the operations.
-- For mathlib convenience, `(+)` is directly defined instead of using `⊗`.

/-- convert a `ℕ` to `satfin (n + 1)`. -/
def of_nat (a : ℕ) : satfin (n + 1) :=
⟨min n a, by simp⟩

/-- convert a `ℕ` to `satfin n`, provided `n` is positive -/
def of_nat' [h : fact (0 < n)] (i : ℕ) : satfin n :=
⟨min (n - 1) i, min_lt_iff.mpr (or.inl (pred_lt (ne_of_gt h)))⟩

@[simp] lemma of_nat_le {a : ℕ} (ha : a ≤ n) : @of_nat n a = ⟨a, lt_succ_of_le ha⟩ :=
by simp [of_nat, ha]

@[simp] lemma of_nat_lt {a : ℕ} (ha : a < n + 1) : @of_nat n a = ⟨a, ha⟩ :=
of_nat_le (le_of_lt_succ ha)

lemma of_nat_zero : @of_nat n 0 = 0 :=
by simp [zero_le]

instance : has_one (satfin (n + 1)) := ⟨of_nat 1⟩

@[simp] lemma coe_one : ((1 : satfin (n + 2)) : ℕ) = 1 :=
by { unfold has_one.one, simp }

lemma val_one : (1 : satfin (n + 2)).val = 1 := by simp

@[simp] lemma mk_one : (⟨1, succ_lt_succ (succ_pos n)⟩ : satfin (n + 2)) = (1 : satfin _) :=
by simp [eq_iff_veq]

protected def add : Π {n}, satfin n → satfin n → satfin n
| 0       ⟨a, ha⟩ _       := absurd ha (not_lt_of_le a.zero_le)
| (n + 1) ⟨a, ha⟩ ⟨b, hb⟩ := ⟨min n (a + b), by simp⟩

instance : has_add (satfin n) := ⟨satfin.add⟩

@[simp] lemma add_def (a b : satfin n) : (((a + b) : satfin n) : ℕ) = min (n - 1) (a + b) :=
begin
  cases n,
  { exact a.elim0 },
  { cases a,
    cases b,
    unfold has_add.add,
    simp [satfin.add] }
end

@[simp] protected lemma add_zero (k : satfin (n + 1)) : k + 0 = k :=
by simp [eq_iff_veq, add_def, k.is_le]

@[simp] protected lemma zero_add (k : satfin (n + 1)) : (0 : satfin (n + 1)) + k = k :=
by simp [eq_iff_veq, add_def, k.is_le]

instance add_comm_monoid (n : ℕ) : add_comm_monoid (satfin (n + 1)) :=
{ add := (+),
  add_assoc := λ a b c, by {
    have hd : ∀ (k l m : ℕ), min m (k + l) = min m (min m k + min m l),
      { intros k l m,
        by_cases ha : k + l ≤ m,
        { have hk : k ≤ m := le_of_add_le_left ha,
          have hl : l ≤ m := le_of_add_le_right ha,
          simp [hk, ha, hl] },
        { sorry },
      },
    simp [eq_iff_veq],
    by_cases ha : a ≤ n,
    by_cases hb : b ≤ n,
    by_cases hc : c ≤ n,
    all_goals {sorry}
  },
  zero := 0,
  zero_add := satfin.zero_add,
  add_zero := satfin.add_zero,
  add_comm := by simp [eq_iff_veq, add_def, add_comm] }

section bit

@[simp] lemma mk_bit0 {m n : ℕ} (h : bit0 m < n) :
  (⟨bit0 m, h⟩ : satfin n) = (bit0 ⟨m, (le_add_right m m).trans_lt h⟩ : satfin _) :=
begin
  cases n,
  { exact absurd h (not_lt_of_le ((bit0 m).zero_le)) },
  { have : m + m ≤ n := by simpa [bit0] using le_of_lt_succ h,
    simp [bit0, eq_iff_veq, this] }
end

@[simp] lemma mk_bit1 {m n : ℕ} (h : bit1 m < n + 1) :
  (⟨bit1 m, h⟩ : satfin (n + 1)) = (bit1 ⟨m, (le_add_right m m).trans_lt
    ((m + m).lt_succ_self.trans h)⟩ : satfin _) :=
begin
  cases n,
  { simpa [bit1, not_lt_of_le] using h },
  { have h1 : m + m + 1 ≤ n + 1,
      { simp [bit1, bit0] at h,
        exact succ_le_of_lt h },
    have h0 : m + m ≤ n + 1 := le_of_add_le_left h1,
    simp [bit1, bit0, eq_iff_veq, h0, h1] }
end

end bit

end add

end basic

end satfin
