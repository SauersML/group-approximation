---
rg: 2
id: leavitt-d4-corrected-short-screens-are-empty
kind: claim
title: Corrected short-unit screens find no shared-triangle or rank-seven collapse
artifacts:
  - research/artifacts/search-degree4-shared-triangle-boundary.py
  - research/artifacts/search-degree4-shared-triangle-boundary.sbatch
  - research/artifacts/search-degree4-length12-rank7-branch-a.py
  - research/artifacts/search-degree4-length12-rank7-branch-a.sbatch
  - research/artifacts/search-degree4-length12-rank7-evolution.py
  - research/artifacts/search-degree4-length12-rank7-evolution.sbatch
---

Two bounded screens have been rerun with actual multiplicative inverses.

First, the length-ten Latin shared-triangle boundary was tested on the
17-element deduplicated library consisting of the elementary packet, its
available inverses, and the short alternating `c,d` ball.  All `17^4=83,521`
assignments reduce to either the identity or a free-product word involving
more than one coefficient copy; no adaptive one-copy mark occurs (MSI job
`16672336`).

Second, the genuine length-twelve rank-seven branch-A projection kernel was
parameterized exactly by

```text
q=r^-1 t^-1,  b=qv,  c=av,  v^2=1,  [v,t]=1.
```

Across the 12-element short library, all `165,888` tuples were inspected;
`117,504` satisfy the commuting filter and `77,460` have a nontrivial adaptive
one-copy projection.  None makes the full free-product boundary a one-copy
word (MSI job `16672532`).  This is a bounded-library fence only, not a
symbolic obstruction to arbitrary Leavitt units.

## Next attack

MSI job `16672971` searches beyond the fixed library by evolving words of
length at most ten in the exact projection parametrization.  It constructs
`v=kck^-1` and takes `t` in its centralizer, so the projection equations hold
identically while fitness is the full free-product reduced length.  This is a
candidate generator, not part of the bounded zero theorem above.
