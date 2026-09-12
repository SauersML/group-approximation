---
rg: 2
id: stw82-oinfinity-stable-extensions-obey-maximum
kind: claim
title: Every extension inside a separable O-infinity-stable algebra obeys the nuclear-dimension maximum formula
distinct_from:
  stw81-oinfinity-envelopes-have-dimension-one-or-infinity: that computes A tensor O-infinity and its hereditary shadows; this treats every ideal-quotient decomposition of an arbitrary O-infinity-stable middle algebra.
  stw82-one-dimensional-middle-forces-maximum: that assumes the middle algebra already has nuclear dimension at most one; this includes nonnuclear middle algebras of infinite nuclear dimension.
artifacts:
  - research/artifacts/stw82-oinfinity-extension-maximum-audit-2026-08-30.md
---

Let

```text
0 -> I -> E -> D -> 0
```

be an extension of separable C-star algebras.  If `E` is
`O_infinity`-stable, then

```text
dim_nuc(E)=max(dim_nuc(I),dim_nuc(D)).
```

No nuclearity assumption is needed.  If `E` is nuclear, every nonzero term
in the extension has nuclear dimension one.  If `E` is nonnuclear, at least
one endpoint is nonnuclear and both sides of the displayed formula are
infinite.
