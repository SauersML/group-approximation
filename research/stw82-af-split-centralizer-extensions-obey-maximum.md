---
rg: 2
id: stw82-af-split-centralizer-extensions-obey-maximum
kind: claim
title: AF split extensions whose section centralizes the ideal obey the nuclear-dimension maximum formula
distinct_from:
  stw82-central-af-split-extensions-obey-maximum: that assumes a commutative AF quotient and a section central in the whole middle algebra; this permits a noncommutative AF quotient and assumes only that the section commutes with the ideal.
  stw82-subhomogeneous-maximum: that assumes both endpoints subhomogeneous; this leaves the ideal arbitrary and imposes a commuting split geometry instead.
artifacts:
  - research/artifacts/stw82-af-split-centralizer-audit-2026-08-30.md
---

Consider a unital extension

`0 -> I -> E --q--> D -> 0`                                   `(ASC1)`

with a unital *-homomorphic section `s : D -> E`.  Suppose `D` is AF and

`[s(D), I] = 0`.                                                `(ASC2)`

Then

`dim_nuc(E) = dim_nuc(I) = max(dim_nuc(I), dim_nuc(D))`.        `(ASC3)`

The quotient need not be commutative and the range of `s` need not lie in
`Z(E)`.  The noncommutative finite-dimensional quotient blocks cannot
interact with the ideal under `(ASC2)`: their ideal corners vanish.  The
remaining scalar blocks give only minimal unitizations of ideal corners.
