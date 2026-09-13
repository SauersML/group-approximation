---
rg: 2
id: tensor-square-nonembedding-from-no-diagonal-conjugacy
kind: route
title: The image of the north--south unit in the second tensor factor would be conjugate to its own diagonal copy
target: no-unital-map-from-leavitt-tensor-square-to-leavitt-over-f2
requires: [leavitt-units-are-not-conjugate-to-diagonal-copies, leavitt-algebras-l-k-1-n-are-simple]
---

Let `L = R = L_(F_2)(1,2)` and suppose `f : L ⊗ L -> L` is unital.

1. Put `u = f(s_0 ⊗ 1) t_0 + f(s_1 ⊗ 1) t_1`. By `tensor-square-nonembedding-from-finite-relative-commutants`,
   step 1, `u` is a unit and `f(x ⊗ 1) = rho_u(x)`.
2. `z = f(1 ⊗ y)` commutes with `u s_i = f(s_i ⊗ 1)`. Hence `u^(-1) z u s_i = s_i z`. Multiplying on the right by
   `t_i` and summing gives `u^(-1) z u = phi(z)`, that is `z = u phi(z) u^(-1)`.
3. `L` is simple (`leavitt-algebras-l-k-1-n-are-simple`), so the unital map `f(1 ⊗ -)` is injective.
4. For the north--south unit `c`, `z = f(1 ⊗ c)` is therefore a unit of infinite order conjugate to `phi(z)`.
   This contradicts `leavitt-units-are-not-conjugate-to-diagonal-copies`. ∎
