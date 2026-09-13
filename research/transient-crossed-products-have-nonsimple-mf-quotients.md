---
rg: 2
id: transient-crossed-products-have-nonsimple-mf-quotients
kind: claim
title: A zero-dimensional crossed product with transient points never has a simple maximal MF quotient of its elementary group
distinct_from:
  toeplitz-subshift-kazhdan-group-has-pestov-mf-quotient: that produces a nontrivial MF radical with a simple maximal MF quotient; this shows crossed products of zero-dimensional systems cannot, which is why that construction is a Toeplitz extension rather than a crossed product.
artifacts:
  - research/artifacts/un-hh-extension-toeplitz-subshift-2026-09-13.md
---

Let `X` be a compact metrizable zero-dimensional space with a homeomorphism `T`, let `Y = CR(T)`, `k = F_2` and
`n >= 4`. Suppose `X != Y`, so the MF radical `EL_n(R_X, I)` of the manuscript's `thm:core-mf-radical` is nontrivial.
Then the maximal MF quotient `EL_n(LC(Y,F_2) x| Z)` is not simple modulo its centre.

So the sandwich shape "nontrivial locally finite radical, simple maximal MF quotient" is invisible to every
zero-dimensional crossed product. It needs a ring whose defect ideal is not a transient part of the dynamics.
