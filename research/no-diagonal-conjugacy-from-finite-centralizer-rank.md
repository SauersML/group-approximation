---
rg: 2
id: no-diagonal-conjugacy-from-finite-centralizer-rank
kind: route
title: Centralizer rank is a conjugacy invariant that quadruples under the diagonal copy
target: leavitt-units-are-not-conjugate-to-diagonal-copies
requires: [leavitt-unit-centralizers-have-finite-rank]
---

Let `y ∈ Q = L_(F_2)(1,2)^x` have infinite order, and put
`rho(y) = dim_(F_2(y)) F_2(y) ⊗_(F_2[y]) C_R(y)`.

1. **Invariance.** `C_R(w y w^(-1)) = w C_R(y) w^(-1)`, and conjugation carries `F_2[y]` onto
   `F_2[w y w^(-1)]`. So `rho` is a conjugacy invariant.
2. **Quadrupling.** Under `R ≅ M_2(R)`, `x -> (t_i x s_j)`, `phi(y)` becomes `diag(y, y)`. So
   `C_R(phi(y)) = M_2(C_R(y))`.
   - `phi` maps `F_2[y]` isomorphically onto `F_2[phi(y)]`, and `phi(p(y)) = diag(p(y), p(y))`.
   - Localizing gives `M_2` of the localization of `C_R(y)`, so `rho(phi(y)) = 4 rho(y)`.
3. **Contradiction.** By `leavitt-unit-centralizers-have-finite-rank`, `1 <= rho(y) < ∞`. If
   `y = w phi(y) w^(-1)`, then `rho(y) = 4 rho(y)`, which is impossible. ∎
