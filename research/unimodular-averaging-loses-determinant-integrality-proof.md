---
rg: 2
id: unimodular-averaging-loses-determinant-integrality-proof
kind: route
title: Compute the two-vertex determinant directly and the ergodic one by Fuglede--Kadison multiplicativity and Jensen's formula
target: unimodular-averaging-loses-determinant-integrality
requires: []
artifacts:
  - research/artifacts/unimodular-networks-mdc-2026-09-12.md
---

Artifact Proposition 2.

1. **Finite network.** `B = [[2,1],[1,3]]` has eigenvalues `(5 ± sqrt 5)/2`.
   The uniform root measure gives `log det = (1/2) log 5` and
   `N_1 = tr B / 2 = 5/2`.
2. **Ergodic network.** In `N(R) = L^infinity({1,2}^Z) x| Z` the operator is
   `T = M_g K M_g` with `K = 2 + s + s^-1`.
   - `det K = exp(2 m(1+z)) = 1`, by Jensen's formula.
   - `det M_g = 2^p`.
   - For `eps > 0`, multiplicativity on invertibles gives
     `det(T + eps M_g^2) = 4^p det(K + eps)`.
   - `T` and `K` are injective. Monotone convergence together with
     `T + eps <= T + eps M_g^2 <= T + 4 eps` gives `det T = 4^p`.
   - `N_1 = 2 E g_0^2 = 2(1 + 3p)`.
