---
rg: 2
id: ternary-anti-central-two-root-defect-has-a-uniform-gap
kind: claim
title: Over anti-central Sylvester rank functions on the ternary Leavitt unit group algebra the two-root defect has an attained positive minimum
distinct_from:
  leavitt-rank-model-defect-gap-on-fixed-point-free-quotients: that is the characteristic-two gap on fixed-point-free quotients of rank ultraproduct models, built from four-generation and range idempotents; this is the characteristic-three gap over abstract anti-central Sylvester rank functions, where anti-centrality replaces the fixed-point-free quotient and the minimum is attained.
  sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one: that is the open assertion that no anti-central Sylvester rank function exists; this bounds the defect of every such function from below, a quantitative corner locality inside that question.
artifacts:
  - research/artifacts/char-three-defect-gap-and-descent-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w5-c3-descent`; independent re-derivation requested from `w4-vf-gate`) by
`ternary-anti-central-defect-gap-proof`.

**Setting.**
* `R = L_(F_3)(1,2)` and `G = R^x = EL_3(R)` through the code `(0, 10, 11)`, with `z = -1` and
  `eps_- = 2(1 - [z])`.
* In `F_3[G]`: `N_ab = [x_ab(1)] - 1` and `D = N_23 N_12`.
* For a prefix `A`: `iota_A(g) = S[A] g T[A] + (1 - S[A]T[A])`, `D_A = F_3[iota_A](D)` and
  `Q_A = 2(1 - [iota_A(z)])`.
* A Sylvester matrix rank function `N` on `F_3[G]` is *anti-central* if `N(eps_-) = 1`.

**Statement.**
1. If an anti-central `N` exists, then `c_3 = min N(D)` over all of them is attained, and `0 < c_3 <= 2/3`.
2. Every Sylvester matrix rank function on `F_3[G]` has `N(D eps_-) >= c_3 N(eps_-)`.
3. Every anti-central `N` has `N(Q_A) = 1/2` and `N(D_A) >= N(D_A Q_A) >= c_3/2` for every nonempty proper
   prefix `A`.
4. Take the functions `X -> rk(sigma(X))` of anti-central rank models into rank ultraproducts over
   characteristic-three fields. Their minimum `c_3^M` is also attained, and `c_3^M >= c_3`.

**Scope.** Items 1 to 3 hold for every abstract Sylvester matrix rank function.
* **Used:** compactness of the space of rank functions, abstract corner locality, the Frobenius inequality
  and commuting compressions.
* **Not needed:** the characteristic-two ingredients that require a regular ring, namely the fixed-point-free
  quotient and displacement through annihilators. `N(eps_-) = 1` already excludes the augmentation rank.

**Payoff.** Combine this with `ternary-cylinder-defect-products-descend-in-sign-sectors` and the open
`ternary-anti-central-disjoint-defects-have-a-strict-deficit`. A minimizer then gives a contradiction, which
is the abstract No branch `sylvester-rank-functions-on-ternary-leavitt-units-kill-minus-one`.
