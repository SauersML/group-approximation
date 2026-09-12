---
rg: 2
id: sylvester-rank-function-quotients-weakly-finite-proof
kind: route
title: Block elimination gives the push-through rank identity, which makes the rank-zero quotient weakly finite
target: sylvester-rank-function-quotients-are-weakly-finite
requires: []
artifacts:
  - research/artifacts/state-upgrade-rank-condition-gap-2026-09-12.md
---

Artifact Section 1.
1. Factor `[[I_n, A],[B, I_m]]` as `[[I_n, 0],[B, I_m]]·[[I_n, A],[0, I_m - BA]]` and as
   `[[I_n, A],[0, I_m]]·[[I_n - AB, 0],[B, I_m]]`. Invertible factors do not change `N`, and the
   triangular blocks with identity diagonal have rank `n + N(I_m - BA)` and `N(I_n - AB) + m`.
2. `N(x + y) <= N(diag(x, y))` and `N(axb) <= N(x)`, so the rank-zero elements form an ideal. It is
   proper because `N(1) = 1`.
3. `N(X) = 0` iff every entry has rank 0, so `N` is constant on cosets of `M_n(ker N)` and faithful on
   the quotient.
4. If `AB - I_n` has rank-zero entries, step 1 gives `N(I_n - BA) = 0`, so `BA = I_n` in the quotient.

No imports.
