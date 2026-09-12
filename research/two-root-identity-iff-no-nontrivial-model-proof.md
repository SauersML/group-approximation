---
rg: 2
id: two-root-identity-iff-no-nontrivial-model-proof
kind: route
title: Matrix units inside the tensor square put the two defect summands in orthogonal Peirce blocks
target: two-root-identity-in-all-models-iff-no-nontrivial-model
requires:
  - el3-unit-root-matrix-units-iff-two-root-identities
artifacts:
  - research/artifacts/cohn-elementary-group-rank-radical-2026-09-12.md
---

Artifact Section 1, Proposition 1.1 and Corollary 1.2.

1. **The tensor square is a model.** At finite level `rk(AB (x) AB - C (x) C) <= 2 rk(AB - C)`, and
   normalized rank is multiplicative on tensors.
2. **Matrix units.** In characteristic two `N_12^2 = 0` is automatic, so `N_23 N_12 = 0` gives
   orthogonal idempotents `p_i` and matrix units `u_ij in p_i M p_j` with `sigma(x_ij(1)) = 1 + u_ij`
   (`el3-unit-root-matrix-units-iff-two-root-identities`). Then `rk(u_ij) = rk(p_i) = rk(N_12)`.
3. **The product.** `N'_ab = u_ab (x) 1 + 1 (x) u_ab + u_ab (x) u_ab`. Every term containing
   `u_23 u_12 = 0` drops, leaving `N'_23 N'_12 = u_23 (x) u_12 + u_12 (x) u_23`.
4. **Ranks add.** The summands have orthogonal left supports `p_2 (x) p_1`, `p_1 (x) p_2` and
   orthogonal right supports `p_3 (x) p_2`, `p_2 (x) p_3`, so the rank is `2 rk(N_12)^2`.
5. **Equivalence.** If every model satisfies the identity, apply step 4 to any model `sigma` and to
   `sigma (x) sigma`: `rk(N_12) = 0`, so `sigma(x_12(1)) = 1`. The element `x_12(1)` normally
   generates `EL_3(S)`, through Weyl conjugates and `[x_ac(1), x_cb(r)] = x_ab(r)`, so `sigma` is
   trivial.

*Verified independently by `w4-vf-gate` (2026-09-12), Section 14.1 of `research/artifacts/gk-vf-gate-verification-2026-09-12.md`. PASS.*
