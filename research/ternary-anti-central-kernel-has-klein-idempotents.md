---
rg: 2
id: ternary-anti-central-kernel-has-klein-idempotents
kind: claim
title: The anti-central evaluation kernel of the ternary Leavitt group algebra contains a Klein idempotent of trace two
distinct_from:
  leavitt-corner-kernel-not-jacobson-radical: that is the binary corner kernel, whose idempotent comes from an order-three unit; over F_3 that element is nilpotent, and this claim uses level-two Klein constants on the anti-central summand instead.
artifacts:
  - research/artifacts/ternary-anti-central-kernel-normal-forms-2026-09-12.md
---

Let `R = L_(F_3)(1,2)`, `G = R^x`, `S = F_3[G]`, `z = -1`, `eps_- = 2(1 - [z])`,
`S_- = eps_- S`, `pi` the evaluation and `K_- = eps_- ker(pi)`. With cylinder idempotents
`q_gamma = S[gamma] T[gamma]`, put

    h1 = s0 t0 - s1 t1,        h2 = -q_00 - q_01 + q_10 - q_11.

Then `h1, h2` are commuting involutions, `z` is not in `H = <h1,h2>`, and

    q = eps_- ([1] + [h1] + [h2] + [h1 h2])

is a nonzero idempotent of `K_-` with Kaplansky trace `tau(q) = 2 = tau(eps_-)`.

Consequences:
* `K_-` is not in the Jacobson radical of `S_-`, so radical perturbation of lifts is dead over
  `F_3`.
* The binary kernel idempotent `[1] + [g] + [g^2]` becomes the square-zero element
  `(1 - [g])^2` for `g = 1 + s0 t1`, so the Klein constants are what replaces it.

Proof: Section 1 of the artifact.
