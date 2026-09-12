---
rg: 2
id: jacobson-ts-cell-excludes-monomial-natural-head-models
kind: claim
title: The Jacobson TS cell excludes all monomial models with a natural head in characteristic two
distinct_from:
  jacobson-ts-cell-is-independent-after-first-raw-commutation: that evaluates the TS word in one amenable seven-ray quotient; this excludes every monomial model with arbitrary natural-head multiplicity over a field of characteristic two.
artifacts:
  - research/artifacts/jacobson-ts-cell-monomial-model-obstruction-2026-09-08.md
---

Let the head `GL_3(F_2)` act on `(k^3 tensor M) direct-sum Y` by its
natural representation on `k^3`, trivially on `Y`, where `k` has
characteristic two and `M!=0`. Use its tensor basis and a basis of `Y`.
There is no representation of the strengthened presentation `Gamma_2`
in which the tail factor and stable involution are monomial operators
in this basis.

More precisely, the finite packet, `h^2=1`, `[h,K]=1`, the first braid
`(hb)^3=1`, and the single TS relation `W=1` already contradict those
model assumptions. Over `F_2`, `W=1` is impossible even without the
first braid. The extra commutation `R=1` and the second braid are not
needed for this obstruction.

This excludes a class of finite or infinite linear models. It proves
neither a complex-unitary matrix gap nor the absence of arbitrary
amenable marked quotients of `Gamma_2`.

DERIVATION
jacobson-ts-cell-monomial-off-diagonal-proof
