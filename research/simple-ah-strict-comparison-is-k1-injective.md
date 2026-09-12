---
rg: 2
id: simple-ah-strict-comparison-is-k1-injective
kind: claim
title: A unital simple AH algebra with strict comparison is K1-injective
invalidates: [stw18-k1-witness-via-ah-lix-upgrade]
distinct_from:
  simple-ah-strict-comparison-is-z-stable: that is Z-stability; this is its nonstable K-theory consequence, the form that decides the K1 route to Problem XVIII.
  stw58-simple-pure-k1-bijective: that assumes pureness and covers all unital simple algebras; this assumes only strict comparison but needs the AH structure.
artifacts:
  - research/artifacts/stw18-k1-route-constraint-map-2026-09-11.md
---

If `A` is a unital simple AH algebra with strict comparison, then
`U(A)/U_0(A) -> K_1(A)` is bijective.

Contrapositively, a unital simple AH algebra that is not K1-injective fails
strict comparison. So no AH algebra, in particular no strict-comparison
upgrade of the LIX towers that keeps homogeneous building blocks, can witness
the K1 route to Problem XVIII. That is why this claim invalidates
`stw18-k1-witness-via-ah-lix-upgrade`.
