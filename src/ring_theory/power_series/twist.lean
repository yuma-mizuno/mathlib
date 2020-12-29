/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

import ring_theory.power_series.basic

/-!
# Twisting formal power series
-/

noncomputable theory

namespace power_series

universe u

variables {R : Type u}

open finset

def twist [comm_ring R] (r : R) : power_series R →* power_series R :=
{ to_fun := λ F, mk (λ n, coeff R n F * r ^ n),
  map_one' := begin
    ext n,
    simp only [coeff_mk, coeff_one],
    split_ifs; simp [h],
  end,
  map_mul' := begin
    intros F G,
    ext n,
    simp only [coeff_mul, coeff_mk, sum_mul],
    apply finset.sum_congr rfl,
    rintros ⟨i, j⟩ h,
    rw nat.mem_antidiagonal at h, dsimp at h,
    subst h, simp [pow_add], ring,
  end }

end power_series
