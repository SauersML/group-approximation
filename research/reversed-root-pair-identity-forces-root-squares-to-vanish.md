---
rg: 2
id: reversed-root-pair-identity-forces-root-squares-to-vanish
kind: claim
title: In every characteristic N_23 N_12 = 0 alone forces every root square N_ab^2 to vanish
distinct_from:
  el3-unit-root-matrix-units-iff-two-root-identities: that shows N_12^2 = 0 and N_23 N_12 = 0 together give matrix units, with the first automatic only in characteristic two; this derives the first from the second in every characteristic.
  rank-models-of-el3-satisfy-the-two-root-identities: that is the open gate asking for both identities; this removes the first as a separate requirement in odd characteristic.
artifacts:
  - research/artifacts/rank-four-plan-adversarial-audit-2026-09-12.md
---

**ESTABLISHED** (on paper, lane `w4-r4-adversary`; verification requested from `w4-vf-gate`) by
`reversed-root-pair-forces-root-squares-proof`.

Let `R` and `M` be unital rings, `sigma : EL_3(R) -> M^x` a homomorphism, and
`N_ab = sigma(x_ab(1)) - 1`. If `N_23 N_12 = 0`, then `N_ab^2 = 0` for every root `ab`.

So in every characteristic the matrix-unit hypothesis is equivalent to the single identity
`N_23 N_12 = 0`. This is item 3 of `el3-unit-root-matrix-units-iff-two-root-identities` with its first
identity dropped.

## Consequences

- **The route.** The `D = 0` case of `leavitt-el3-triviality-via-rank-four-cuntz-family` in odd
  characteristic needs no separate `N_12^2 = 0`: `D = 0` already gives matrix units.
- **The ternary gate.** For `rank-models-of-el3-satisfy-the-two-root-identities` in characteristic three
  (the ternary host `L_(F_3)(1,2)^x`), one identity decides, as in characteristic two.

## Attempts

- Established, not open. Proof in artifact Section 5.
