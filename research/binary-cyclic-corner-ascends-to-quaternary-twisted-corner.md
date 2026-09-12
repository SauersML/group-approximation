---
rg: 2
id: binary-cyclic-corner-ascends-to-quaternary-twisted-corner
kind: route
title: Multiply the binary corner solution by the visible scalar idempotent over F_4
target: leavitt-visible-cyclic-corner-is-full-on-some-host
requires:
  - binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
artifacts:
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

Proposition 3.1(3) of the artifact.
- `R^x = L_(F_2)(1,2)^x` is a subgroup of `G = L_(F_4)(1,2)^x`, so `F_2[R^x]` sits inside `F_4[G]`.
- `eps_iota = [1] + ω² [ω] + ω [ω²]` is central in `F_4[G]`, so `x -> x eps_iota` is a unital ring map
  into the visible factor. It sends `e = 1 + [g] + [g²]` to `e_1 = (1 + [g] + [g²]) eps_iota`.
- A solution `c e b = 1` becomes `(c eps_iota) e_1 (b eps_iota) = eps_iota`: the corner at
  `(q, d, m) = (4, 2, 3)`, where `3 | q − 1` and 3 is admissible for `d = 2`.
