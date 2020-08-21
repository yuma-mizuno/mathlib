-- construction of structure sheaf

import algebraic_geometry.prime_spectrum
import ring_theory.localization
import algebraic_geometry.presheafed_space
import algebra.category.CommRing

universe u

variables {R : Type u} [comm_ring R]

-- #check of -- root namespace!

/- f is defined by an element of R_s on U ∩ D(s) -/
def is_locally_allowable (s : R) (U : set (prime_spectrum R))
  (f : Π {P : prime_spectrum R} (hP : P ∈ U), localization.at_prime P.1) : Prop :=
∃ r : R,
∀ (Q : prime_spectrum R) (hQ : Q ∈ U) (hs : ¬ (s ∈ Q.1)),
  f hQ * (localization.of _).to_map s = (localization.of _).to_map r

/-- Definition of sections of O_X on an open U of Spec(R) -/
def sections (U : set (prime_spectrum R)) :=
-- functions sending each P in U to an element of R_P
{ f : Π {P : (prime_spectrum R)} (hP : P ∈ U), localization.at_prime P.1 //
-- such that
  ∀ (P : prime_spectrum R) (hP : P ∈ U), ∃ s : R, ¬ (s ∈ P.1) ∧
  is_locally_allowable s U @f
}

namespace sections

variables {U : set (prime_spectrum R)}

-- am I right in thinking that we don't need U to be open for any of this?

--(hU : prime_spectrum.zariski_topology.is_open U)

def zero : sections U := ⟨λ P hP, 0, sorry⟩

instance : has_zero (sections U) := ⟨sections.zero⟩

def one : sections U := ⟨λ P hP, 1, sorry⟩

instance : has_one (sections U) := ⟨sections.one⟩

def add (a b : sections U) : sections U :=
⟨λ P hP, a.1 hP + b.1 hP, sorry⟩

instance : has_add (sections U) := ⟨sections.add⟩

def neg (a : sections U) : sections U :=
⟨λ P hP, -a.1 hP, sorry⟩

instance : has_neg (sections U) := ⟨sections.neg⟩

def mul (a b : sections U) : sections U :=
⟨λ P hP, a.1 hP * b.1 hP, sorry⟩

instance : has_mul (sections U) := ⟨sections.mul⟩

instance : comm_ring (sections U) :=
{ add := (+),
  add_assoc := sorry,
  zero := 0,
  zero_add := sorry,
  add_zero := sorry,
  neg := has_neg.neg,
  add_left_neg := sorry,
  add_comm := sorry,
  mul := (*),
  mul_assoc := sorry,
  one := 1,
  one_mul := sorry,
  mul_one := sorry,
  left_distrib := sorry,
  right_distrib := sorry,
  mul_comm := sorry }

end sections

-- need functoriality

def restrict {U V : set (prime_spectrum R)} (hVU : V ⊆ U) : sections U →+* sections V :=
{ to_fun := λ a, ⟨λ P hP, a.1 (hVU hP), sorry⟩,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

-- make the presheafed space -- still not done

#exit

def Spec (R : Type u) [comm_ring R] : algebraic_geometry.PresheafedSpace CommRing :=
{ to_Top := Top.of (prime_spectrum R),
  𝒪 := {
    -- this doesn't work
    obj := λ U, CommRing.of (sections (U.val : set (prime_spectrum R))),
    -- so I can't write this
    map := sorry,
    map_id' := sorry,
    map_comp' := sorry } }


/-

thoughts

R_f → R_P gives me a local section which is continuous

R_f has a map to Π (P ∈ D(f)), R_P (*)

The image of R_f in Π (P ∈ D(f), R_P) is "locally allowable sections"

and the image of this map is some space of "allowable sections"
  and we glue all the allowable sections to get the sheaf

O_X(U) is {f : Π (P ∈ U), R_P | f is locally of this (*) form}


localization.at_prime (aka P ↦ R_P) is a function

E := Σ P, R_P is a sigma type

The sheaf is the continuous sections

Given F sending P to R_P (a sigma type)
I need to understand the continuous sections of Σ

-/
