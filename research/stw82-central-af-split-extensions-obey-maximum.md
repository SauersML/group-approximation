---
rg: 2
id: stw82-central-af-split-extensions-obey-maximum
kind: claim
title: Centrally split extensions by commutative AF quotients obey the nuclear-dimension maximum formula
distinct_from:
  stw82-af-split-centralizer-extensions-obey-maximum: that strengthens this theorem to arbitrary AF quotients whose section merely centralizes the ideal; the present statement is its commutative central special case.
  stw82-subhomogeneous-maximum: that assumes both endpoints are subhomogeneous and allows nonsplit extensions; this allows an arbitrary ideal and instead uses a central section of a zero-dimensional quotient.
  stw82-zero-dimensional-central-supports-recolour-pointwise: that is a local colour-reuse theorem conditional on a common central support algebra; this derives an actual extension formula by a finite-clopen-stage decomposition.
artifacts:
  - research/artifacts/stw82-central-af-split-extension-audit-2026-08-30.md
---

Consider a unital extension

`0 -> I -> E --q--> D -> 0`                                   `(CAS1)`

with a unital *-homomorphic section `s : D -> Z(E)`.  If `D` is a
commutative AF algebra, then

`dim_nuc(E) = dim_nuc(I) = max(dim_nuc(I), dim_nuc(D))`.        `(CAS2)`

No quasidiagonality of the extension and no projectional quasicentral
approximate unit are assumed.  The central section instead lets finite
clopen quotient stages split the whole middle algebra into unitizations of
ideal corners, with no extra approximation colour.

The stronger theorem
`stw82-af-split-centralizer-extensions-obey-maximum` shows that the quotient
may be noncommutative AF if the section is only required to centralize the
ideal.  Its extra matrix-block argument proves that every noncommutative
finite-dimensional quotient block has zero ideal corner.
