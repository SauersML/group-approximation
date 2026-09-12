---
rg: 2
id: non-hyperlinear-group-via-nonzero-schur-kernel
kind: route
title: A Schur class killed by a nonsingular equation gives a non-hyperlinear central extension
target: non-hyperlinear-group
requires: [some-nonsingular-equation-has-nonzero-schur-kernel, schur-kernel-lies-in-hyperlinear-radical]
artifacts:
  - research/artifacts/kl-schur-kernel-central-extensions-2026-09-11.md
---

Let `0 != x` be killed. `Q/Z` is an injective cogenerator, so some
`gamma : H_2(Q) -> Q/Z` has `gamma(x) != 0`. Universal coefficients realize
`gamma` as the multiplier of a countable central extension `E` of `Q` by
`Q/Z`. The second prerequisite puts `gamma(x) != 1` in `Rad_hyp(E)`, so
`E` is not hyperlinear. If the certificate is explicit, so is `E`: replace
`Q/Z` by a finite cyclic quotient detecting `x` when the Schur multiplier
is finitely generated.
