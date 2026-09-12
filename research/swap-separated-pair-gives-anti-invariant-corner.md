---
rg: 2
id: swap-separated-pair-gives-anti-invariant-corner
kind: route
title: Average the partner of a swap-separated pair over the swap to invert the corner idempotent
target: ternary-anti-invariant-swap-corner-is-full
requires:
  - ternary-twisted-algebra-has-swap-separated-one-sided-pair
  - ternary-leavitt-swap-problem-splits-at-central-involution
artifacts:
  - research/artifacts/gk-vf-linear-verification-2026-09-12.md
  - research/artifacts/ternary-swap-separated-pairs-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

## Why sufficient

Let `c a = eps_-` and `c [w] a = 0` in `S_-`.

* `ternary-leavitt-swap-problem-splits-at-central-involution` supplies
  `e_- = eps_- . 2(1 + [w])`, and `[w]` is an involution.
* Put `b = a` and `c' = c(1 + [w])`.
* Since `(1 + [w])^2 = 2(1 + [w])`, we get
  `c' e_- b = 4 c (1 + [w]) a = c a + c [w] a = eps_-`.

This is one half of an equivalence. The reverse route is
`anti-invariant-corner-gives-swap-separated-pair`, so the dependency cycle is deliberate. Theorem 1 of
the artifact.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 27 of the verification artifact).

*Verified independently by `gk-vf-linear` (2026-09-12). The identity `c' e_- b = 4 c(1 + [w]) a = eps_-` was re-derived from `(1 + [w])^2 = 2(1 + [w])` and `4 = 1`. See Section 1 of the linear-family verification artifact.*
