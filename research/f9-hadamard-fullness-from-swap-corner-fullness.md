---
rg: 2
id: f9-hadamard-fullness-from-swap-corner-fullness
kind: route
title: A swap corner solution conjugated by a constant F_9 unit solves the Hadamard spectral corner
target: f9-hadamard-spectral-idempotent-is-full
requires:
  - ternary-anti-invariant-swap-corner-is-full
  - hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent
artifacts:
  - research/artifacts/hadamard-spectral-conjugacy-and-forced-states-2026-09-12.md
---

Corollary 1.4 of the artifact. Given `c e_- b = eps_-` in `S_-`, view it in `S_-^(9)`. With `f_+ = W e_- W^(-1)`,
`(c W^(-1)) f_+ (W b) = c e_- b = 1_-`.

**Intended equivalence cycle. Do not delete any link.** Cairn check reports this region cycle, and it is correct.
All four claims on it are equivalent, and all are OPEN. Each link is a valid implication:

| route | proves | from | verified |
|---|---|---|---|
| `f9-hadamard-fullness-from-swap-corner-fullness` (this route) | `f9-hadamard-spectral-idempotent-is-full` | `ternary-anti-invariant-swap-corner-is-full` | w4-vf-linear-b, Section 9 of `gk-vf-linear-b-verification-2026-09-12.md` |
| `anti-central-cohn-family-gives-swap-corner-fullness` | `ternary-anti-invariant-swap-corner-is-full` | `ternary-anti-central-summand-has-cohn-family` | gk-vf-linear, Section 15 |
| `f9-cohn-family-descends-to-anti-central-summand` | `ternary-anti-central-summand-has-cohn-family` | `ternary-anti-central-cohn-family-over-f9` | w3-vf-linear, Section 6.1 |
| `hadamard-spectral-fullness-gives-f9-cohn-family` | `ternary-anti-central-cohn-family-over-f9` | `f9-hadamard-spectral-idempotent-is-full` | w3-vf-linear, Section 6.2 |

The Hadamard spectral corner and the swap corner are the same problem. Neither direction establishes any claim
on the cycle alone.

*Verification by `w4-vf-linear-b` (2026-09-12), Sections 9 and 27 of `research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`: PASS as an implication. `(c W^-1)(W e_- W^-1)(W b) = c e_- b`.*
