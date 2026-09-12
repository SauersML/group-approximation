---
rg: 2
id: global-v4-capacity-via-exclusive-tags
kind: route
title: Convert shared exclusive tags into the global V4 exit-capacity ledger
target: globally-conditioned-v4-exit-capacity
requires:
  - shared-context-exclusive-v4-tagging
  - disjoint-tag-covariance-controls-cross-gram
  - global-v4-exit-capacity-is-cross-gram-curvature
---

Apply `disjoint-tag-covariance-controls-cross-gram` to the joint decoder of
`shared-context-exclusive-v4-tagging`.  Its source conditions give the
partial-isometry sources `(VGC1)`.  Tag exclusivity bounds the total
off-parent leakage, pairwise disjoint tag types bound the complete ordered
cross-Gram overlap, and `(SCT2)` charges their sum to the shared defining
relator energy:

```text
l+o <= ((4N-3)/kappa(H,S)) C E_rel+o(1).              (1)
```

This is `(VGC5)`.  The five-fourths source identity and
`global-v4-exit-capacity-is-cross-gram-curvature` then give the fixed density
payment `(GVC3)`.  Because the tag decoder is joint before context separation,
the result does not factor through scalar forbidden masses and does not invoke
the circular single-context capacity theorem.  The retained exact tracial
extension supplies completeness.
