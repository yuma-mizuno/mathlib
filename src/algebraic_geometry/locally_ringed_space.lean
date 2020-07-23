-- locally ringed spaces

import tactic

import topology.basic
import algebraic_geometry.presheafed_space
import algebra.category.CommRing

open algebraic_geometry
structure ringed_space :=
(X : PresheafedSpace CommRing)
-- is a sheaf
