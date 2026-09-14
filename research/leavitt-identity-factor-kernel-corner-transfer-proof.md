---
rg: 2
id: leavitt-identity-factor-kernel-corner-transfer-proof
kind: route
title: Amplify onto level-k cylinders and multiply by a diagonal-constant character idempotent missed by the evaluation
target: leavitt-identity-factor-failures-transfer-into-kernel-corners
requires: [leavitt-unit-group-algebras-split-over-scalar-characters]
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Section 7 of the artifact.
* `delta_k` is an injective homomorphism. It fixes the scalars, commutes with the diagonal
  constants, and meets them only in the scalars.
* `|H|` is prime to `p`, so `E` is an idempotent. Orthogonality of characters gives
  `pi(E) = sum_(ev_gamma|H = psi) q_gamma = 0`.
* `H n Z = 1` makes `(g, h) -> delta_k(g) h` injective, so `mu` is injective.
* The level criterion counts `(q-1)^(d^k - 1)` characters of `{lambda : lambda(0^k) = 1}` against at
  most `d^k` coordinate characters. The case `(3,2)` at level `1` is checked by listing subgroups.
* Base change: `eps' = ((q-1)/(q'-1)) sum_t t^(-1)[t] eps_iota` over disjoint cosets `t G_q`.
