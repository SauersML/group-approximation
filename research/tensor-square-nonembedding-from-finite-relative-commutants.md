---
rg: 2
id: tensor-square-nonembedding-from-finite-relative-commutants
kind: route
title: The second tensor factor lands in the relative commutant of the first, and no finite-dimensional algebra receives a unital copy of L
target: no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2
requires: [leavitt-endomorphism-relative-commutants-are-finite]
---

Let `L = R = L_(F_2)(1,2)`, and suppose `f : L ⊗ L -> L` is a unital homomorphism.

1. Put `u = f(s_0 ⊗ 1) t_0 + f(s_1 ⊗ 1) t_1` and `u' = s_0 f(t_0 ⊗ 1) + s_1 f(t_1 ⊗ 1)`.
   - The relations of `L` give `u u' = Σ_i f(s_i ⊗ 1) f(t_i ⊗ 1) = 1` and `u' u = Σ_i s_i t_i = 1`.
   - They also give `f(s_i ⊗ 1) = u s_i` and `f(t_i ⊗ 1) = t_i u^(-1)`.
   - So `f(x ⊗ 1) = rho_u(x)` for all `x`.
2. `f(1 ⊗ y)` commutes with `f(x ⊗ 1)`, so `B = f(1 ⊗ L)` is a unital subalgebra of `C_u = C_R(rho_u(R))`.
3. `B` is the image of a unital map from `L`. Through `b -> (b f(1 ⊗ s_0), b f(1 ⊗ s_1))`, with inverse
   `(a, c) -> a f(1 ⊗ t_0) + c f(1 ⊗ t_1)`, it satisfies `B ≅ B ⊕ B` as a left `B`-module.
4. So `dim B = 2 dim B`, and `B != 0` because it contains `1`. Hence `B`, and with it `C_u`, is
   infinite-dimensional. This contradicts `leavitt-endomorphism-relative-commutants-are-finite`. ∎
