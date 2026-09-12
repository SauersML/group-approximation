---
rg: 2
id: binary-cyclic-corner-fullness-gives-kaplansky-failure
kind: route
title: Cut the full averaging idempotent into a strict one-sided pair
target: leavitt-unit-group-algebra-not-directly-finite
requires:
  - binary-cyclic-averaging-idempotent-is-full-on-leavitt-units
artifacts:
  - research/artifacts/w3-vf-linear-verification-2026-09-12.md
  - research/artifacts/quaternary-twisted-corner-census-2026-09-12.md
---

Proposition 3.1(2) of the artifact. If `c e b = 1` with `e = 1 + [g] + [g²]`, put `α = c e` and
`β = e b`. Then `α β = c e b = 1`. If `β α = 1`, then `e = e (β α) = β α = 1`, so `[g] = [g²]` in
`F_2[R^x]`, which is false because `g` has order three.

*Verification by `w3-vf-linear` (2026-09-12), Section 2.2 of `research/artifacts/w3-vf-linear-verification-2026-09-12.md`: PASS. e = 1 + [g] + [g^2] is idempotent in characteristic two, and beta alpha = 1 would force [g] = [g^2].*
