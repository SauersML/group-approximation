---
rg: 2
id: sylvester-rank-functions-on-leavitt-units-are-regular
kind: claim
title: Every Sylvester rank function on the binary Leavitt unit group algebra comes from a faithful regular rank ring
distinct_from:
  sylvester-rank-functions-on-leavitt-units-kill-two-root-defect: that asks every rank function to kill the two-root defect; this asks every rank function to factor through a von Neumann regular ring with a faithful rank function, which transfers the regular-ring defect chain to all rank functions.
artifacts:
  - research/artifacts/rank-gate-axiom-audit-2026-09-12.md
---

**OPEN.** Let `R = L_(F_2)(1,2)`. Every Sylvester matrix rank function `rk` on `F_2[R^x]` has the form
`rk = rk_U o phi` on matrices, for a unital ring homomorphism `phi : F_2[R^x] -> U` into a von Neumann
regular ring `U` with a faithful Sylvester matrix rank function `rk_U`.

**Why it matters.** `leavitt-defect-descent-chain-holds-in-regular-rank-rings` puts the whole defect
chain in faithful regular rank rings. With this claim, any triviality proof valid in that class (for
example strict submultiplicativity of disjoint-cylinder defects, artifact Consequence 3.2) proves
`sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`, and so decides
`binary-leavitt-units-carry-nonaugmentation-rank-function` negatively, not only linear soficity.

## Attempts

- 2026-09-12 `w4-upg-audit` (artifact Section 4.3): the regular rank functions form a closed convex set
  containing the augmentation rank, every matricial rank function, and every rank function through a
  matrix algebra over a division ring.
  - Convexity through products `U_1 x U_2`.
  - Closure through ultraproducts of faithful regular rank rings modulo their null ideals.
  - So the claim fails exactly when some rank function lies outside this closed convex set. No candidate
    is known.
- The literature status (whether every Sylvester matrix rank function on every ring is regular) was not
  checked against any source read locally. [SYL] Corollary 4 records that the stronger matricial
  statement is not known.
- The null-ideal quotient `B = F_2[R^x]/I_rk` need not be regular, so the envelope has to be built, not
  read off.
