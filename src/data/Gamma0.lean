import algebra.linear_ordered_comm_group_with_zero

universe u

def Γ₀ := with_zero (multiplicative ℤ)

namespace Γ₀

instance : comm_group_with_zero Γ₀ := show comm_group_with_zero (with_zero (multiplicative ℤ)), by apply_instance
instance : linear_order Γ₀ := show linear_order (with_zero _), by apply_instance
instance : ordered_comm_monoid Γ₀ := show ordered_comm_monoid (with_zero _), by apply_instance

instance : linear_ordered_comm_group_with_zero Γ₀ :=
{ mul_le_mul_left := with_zero.mul_le_mul_left,
  zero_le_one := with_zero.zero_le 1,
  ..Γ₀.comm_group_with_zero,
  ..Γ₀.linear_order,
  ..Γ₀.ordered_comm_monoid }

instance : has_coe (multiplicative ℤ) Γ₀ := ⟨some⟩

def q : Γ₀ := multiplicative.of_add 1
def qu : units Γ₀ := ⟨(multiplicative.of_add 1 : multiplicative ℤ), (multiplicative.of_add (-1 : ℤ) : multiplicative ℤ),
  begin
    simp
  end,
  begin
    simp,
  end⟩

def qu_n (n : ℤ) : (qu ^ n : Γ₀) = (multiplicative.of_add n : multiplicative ℤ) :=
begin
  unfold qu,
  dsimp,
  unfold has_pow.pow,
  delta fpow,
  simp,
  sorry,
end

--need to show it's a universal object

--#print prefix option

def lift {X : Type u} [monoid_with_zero X] (v : units X) : Γ₀ →* X :=
{ to_fun := λ g, option.rec 0 (λ n, ((v ^ (multiplicative.to_add n) : units X) : X)) g,
  map_one' := rfl,
  map_mul' := begin
    rintro (_ | x) (_ | y),
    { suffices : @option.rec (multiplicative ℤ) (λ _, X) (0 : X) (λ n, ((v ^ (multiplicative.to_add n) : units X) : X)) (none : Γ₀) = (0 : X),
        convert this, simp, },
    { suffices : @option.rec (multiplicative ℤ) (λ _, X) (0 : X) (λ n, ((v ^ (multiplicative.to_add n) : units X) : X)) (none : Γ₀) = (0 : X),
      convert this, simp, },
    { suffices : @option.rec (multiplicative ℤ) (λ _, X) (0 : X) (λ n, ((v ^ (multiplicative.to_add n) : units X) : X)) (none : Γ₀) = (0 : X),
      convert this, simp, },
    { suffices : @option.rec (multiplicative ℤ) (λ _, X) (0 : X) (λ n, ((v ^ (multiplicative.to_add n) : units X) : X)) ((x * y : multiplicative ℤ) : Γ₀) =
        (v ^ x.to_add : units X) * (v ^ y.to_add : units X),
      convert this, norm_cast,
      suffices : ((v ^ ((x * y).to_add : ℤ) : units X) : X) = (v ^ x.to_add : units X) * (v ^ y.to_add : units X),
        convert this,
      have h := (gpow_add v x.to_add y.to_add),
      norm_cast,
      convert h
    },
  end }

variables {X : Type u} [monoid_with_zero X] (v : units X)

lemma lift_zero : lift v 0 = 0 := rfl
lemma lift_int (n : ℤ) : lift v (qu^n) = ((v : units X)^n : units X) :=
begin
  unfold lift,
  simp,
  sorry
end

lemma lift_q : lift v q = v :=
begin
  let Z := ((v^(1 : ℤ) : units X) : X) = v,
  suffices : Z,
    convert this,
  sorry,
  sorry
end

end Γ₀
