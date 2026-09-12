---
rg: 2
id: leavitt-d4-length12-low-rank-systems-are-nonclosing-proof
kind: route
title: Apply the chirality test before ranking coefficient projections
target: leavitt-d4-length12-low-rank-systems-are-nonclosing
requires:
  - leavitt-triangle-carrier-chirality-criterion
  - leavitt-d4-length12-rank8-nine-cyclic-classes
---

The unfiltered rank census has six rank-seven and forty-two rank-eight
systems.  The rank-seven chiralities are `(N,N,I)` and `(I,N,I)`.  The nine
cyclic rank-eight classes have chiralities among

```text
(I,N,I), (N,I,I), (N,I,N), (N,N,I).
```

Every tuple is mixed, so the chirality criterion excludes all forty-eight
systems from the coefficient-only compiler.

The corrected `--balanced-only` mode of
`research/artifacts/rank-degree4-length12-triangles.py` checks carrier signs
before accepting a rank system.  On `---+-+++++++` it gives

```text
rank 9: 12, rank 10: 201, rank 11: 1008, rank 12: 399,
```

with no balanced system below rank nine.  The prior branch-A and branch-B
short-packet censuses remain valid bounded normal-form data, but their mixed
orientations cannot be interpreted as terminal coefficient relations.

