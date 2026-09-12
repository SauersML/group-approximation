---
rg: 2
id: stw83-canonical-circle-toeplitz-dimension-two-bound
kind: claim
title: The canonical circle-by-circle Toeplitz family has nuclear dimension one or two
artifacts:
  - research/artifacts/stw83-lxxxiii-graph-nuclear-dimension-audit-2026-08-30.md
distinct_from:
  stw83-circle-connector-canonical-full-corner: that identifies the canonical full corner but does not give a nuclear-dimension bound for it.
  stw83-two-non-k-extension-directions-remain-open: that records the unresolved two-colour problem; the present theorem narrows the canonical circle-by-circle value to two possibilities.
---

For `N>=1`, put

```text
A_N=C*(S^N tensor 1, K tensor C(T))
    subset M(K tensor C(T)).
```

Then

```text
1 <= dim_nuc(A_N) <= 2.                                  (1)
```

Consequently, every finite graph covered by
`stw83-circle-circle-boundary-index` has nuclear dimension at most two.

The upper bound is a three-colour, coefficient-valued adaptation of the
Brake--Winter Toeplitz approximation.  It improves the generic extension
estimate, which only gives three from an ideal and quotient of nuclear
dimension one.  It does not prove that the third colour can be removed, so the
dimension-one part of Problem LXXXIII remains open for this family.
