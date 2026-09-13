---
rg: 2
id: bs-1-n-does-not-embed-in-pl-plus-interval-proof
kind: route
title: The conjugator fixes a bump endpoint of a, where slope lambda must equal lambda^n
target: bs-1-n-does-not-embed-in-pl-plus-interval
requires: []
artifacts:
  - research/artifacts/zp-pl-interval-subgroup-obstructions-2026-09-13-part1.md
---

Full derivation in the artifact, §N2. `a^n` and `a` have the same bumps, and `t` maps the
bumps of `a` onto those of `t a t^{-1} = a^n`. So `t` permutes the finitely many bumps of
`a` order-preservingly and fixes each. At the left endpoint `p` of a bump, `t(p) = p` and
`λ = a'(p+) ≠ 1`. The chain rule gives `λ = (t a t^{-1})'(p+) = (a^n)'(p+) = λ^n`, so
`λ = 1`, a contradiction.
