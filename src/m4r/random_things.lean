import algebra.homology.homology algebra.category.Module.abelian tactic.linarith

universes u v

def is_projective
  (R : Type u) [ring R] (M : Type u) [add_comm_group M] [module R M] :
-- M is the R-module on which `projective` is a predicate
  Prop := -- `projective R M` is a proposition
∃ i : M →ₗ[R] (M →₀ R), function.injective i ∧
∃ q : submodule R (M →₀ R), is_compl q i.range

theorem universal_property {R A B M : Type u} [ring R] [add_comm_group M] [semimodule R M]
  (h : is_projective R M)
[add_comm_group A] [add_comm_group B]
  [module R A] [module R B] [add_comm_group M] [semimodule R M] (f : A →ₗ[R] B) (g : M →ₗ[R] B) : -- the R-linear maps
function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g :=
begin
  sorry
end

theorem is_projective_of_universal_property
  {R M : Type u} [ring R] [add_comm_group M] [semimodule R M]
(huniv : ∀ {A B : Type u} [add_comm_group A] [add_comm_group B], by exactI ∀
[module R A] [module R B], by exactI
∀ (f : A →ₗ[R] B) (g : M →ₗ[R] B), -- the R-linear maps
function.surjective f → ∃ (h : M →ₗ[R] A), f.comp h = g) : is_projective R M := sorry

def chain_complex.pure (R M : Type u) [ring R] [add_comm_group M] [semimodule R M] : chain_complex (Module R) :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl }

structure projective_resolution (R : Type u) [comm_ring R] (M : Type u)
  [add_comm_group M] [module R M] :=
(complex : chain_complex (Module R))  -- `Module R` with a capital M is the type of objects in
-- the category of R-modules.
(bounded : ∀ (n : ℤ), n < 0 → subsingleton (complex.X n)) -- The modules to the right of the
-- zeroth module are trivial.
(projective : ∀ (n : ℤ), is_projective R (complex.X n))
(resolution : complex ≅ chain_complex.pure R M)
--(coker_isom : (homological_complex.homology (Module R) 0).obj complex ≅ Module.of R M)
-- The homology at the zeroth module (the cokernel of the map P₁ → Pₒ) is isomorphic to M.

--lemma projective_of_subsingleton (R : Type u) [comm_ring R] [M] (subsingleton M):
--is_projective R M

def projective_resolution_of_projective (R : Type u) [comm_ring R] (M : Type u)
  [add_comm_group M] [module R M] (H : is_projective R M) :
  projective_resolution R M :=
{ complex :=
  { X := λ n, if n = 0 then Module.of R M else Module.of R punit,
    d := λ n, 0,
    d_squared' := rfl },
  bounded := λ n hn, -- let n ∈ ℤ be negative
  begin
    dsimp,
    rw if_neg (int.ne_of_lt hn), -- apply the fact that n cannot be 0
    exact punit.subsingleton,
  end,
  projective := λ n,
  begin
    dsimp,
    split_ifs, -- split into the cases n = 0 and n ≠ 0
    { rwa if_pos h }, -- apply the assumptions that n = 0 and M is projective
    { rw if_neg h, -- apply the assumption n ≠ 0
      sorry }
  end,
  resolution := category_theory.iso.refl _ }
