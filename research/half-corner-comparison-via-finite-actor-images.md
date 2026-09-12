---
rg: 2
id: half-corner-comparison-via-finite-actor-images
kind: route
title: Build the chart comparison from actors with a finite coordinate interpretation
target: half-corner-chart-comparison-exists
requires: []
artifacts:
  - research/artifacts/kaplansky-half-corner-feedback-and-projective-defects-2026-09-08.md
  - research/artifacts/kaplansky-torus-fusion-brauer-balance-2026-09-11.md
---

**Dead.** Invalidated by `chart-comparison-must-fuse-torus-classes`.

The approach: choose `Z, L` as words in the finite chart and in root elements
with Leavitt coefficients whose generated group admits a finite coordinate
interpretation, a homomorphism to some `GL_m(F_4)` which is injective on `K` and
in which `K` acts through natural `F_4`-blocks plus trivial coordinates. The
recorded instances are the Jacobson one-pair specialization `s = t = 1`
(half-corner Section 10), packed Cuntz actors after the rectangular isomorphism
`M_4 -> M_3` (Section 11), the literal two-pair formula after the `3 -> 5`
coordinate expansion (Section 12), and creation-only actors specialized at
`s_0 = s_1 = 0` (Section 14).

In any such image `T0 = diag(w, w^2)` moves two `F_4`-coordinates of each natural
block and `T1, T2` move one. They are not conjugate, so the balance of induced
Brauer characters fails and no comparison exists, whatever the coefficients,
the supports or the left inverse's support.

This route is recorded with `requires: []` only so the invalidation has a
target; it asserts nothing while its invalidator is established.
