import model_theory.substructure
import data.pfun

universe u

variables {L : Language.{u}} {μ ν : Type u} {M : Structure L μ} {N : Structure L ν}

structure partial_first_order_embedding :=
(to_pfun : μ →. ν)
(map_rel : ∀ {n : ℕ} (r : L.relations n) (x : fin n → μ) (hx : ∀ i, x i ∈ to_pfun.dom), 
  M.rel_map r x = N.rel_map r (λ i, to_pfun.fn (x i) (hx i)))
(map_fun : ∀ {n : ℕ} (f : L.functions n) (x : fin n → μ) (hx : ∀ i, x i ∈ to_pfun.dom)
  (hfx : M.fun_map f x ∈ to_pfun.dom),
  to_pfun.fn (M.fun_map f x) hfx = N.fun_map f (λ i, to_pfun.fn (x i) (hx i)))

