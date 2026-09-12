---
rg: 2
id: ternary-anti-central-cohn-family-over-f9
kind: claim
title: The anti-central summand of the F_9 group algebra of the ternary Leavitt unit group has a unital two-pair Cohn family
distinct_from:
  ternary-anti-central-summand-has-cohn-family: that asks for the family with F_3 coefficients; this allows F_9 coefficients on the same group, and the two are equivalent through the unital homomorphism Phi of the artifact, so this node records the enlarged search space rather than a weaker target.
artifacts:
  - research/artifacts/f9-hadamard-spectral-cohn-attempt-2026-09-12.md
---

**OPEN.** Let `G = L_(F_3)(1,2)^x`, `z = -1`, and `S_-^(9) = eps_- F_9[G]` with unit `1_- = eps_-`.
Exhibit `sigma_1, sigma_2, tau_1, tau_2` in `S_-^(9)` with `tau_i sigma_j = delta_ij 1_-`.

**Equivalent to the F_3 claim** (Theorem 1.1 of the artifact). The regular representation of `F_9`
over `F_3`, followed by the unital embedding `M_2(S_-) -> S_-` of
`anti-central-ternary-summand-contains-its-matrix-ring`, is a unital ring homomorphism
`S_-^(9) -> S_-`. So a family here gives one in `S_-`. Two routes record the equivalence as an
intended cycle: `f9-cohn-family-descends-to-anti-central-summand` and
`anti-central-cohn-family-extends-to-f9`.

## Attempts

- *Hadamard spectral idempotents* (artifact Section 2). `f_+ = 2(1 + i[h])` for the depth-one Hadamard
  unit `h` is a half idempotent, conjugated to its complement by the constant unit
  `u = s0 t0 + s1 t0 - s1 t1`. So `f9-hadamard-spectral-idempotent-is-full` suffices, through
  `hadamard-spectral-fullness-gives-f9-cohn-family`.
- *Where it dies today.* No finitely supported `b, c` with `c f_+ b = 1_-` are known. The support
  subgroup must admit no characteristic-three rank model moving `z` (Proposition 2.3 of the artifact).
