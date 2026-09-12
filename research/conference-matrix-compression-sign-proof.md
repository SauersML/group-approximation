---
rg: 2
id: conference-matrix-compression-sign-proof
kind: route
title: Rotate even cube characters by a four-by-four conference matrix
target: compression-signs-alone-do-not-fix-joint-multiplicity
requires: []
---

One may take

```text
C=[[0, 1, 1, 1],
   [1, 0, 1,-1],
   [1,-1, 0, 1],
   [1, 1,-1, 0]].
```

Its rows are orthogonal and have squared norm three.  Match the zero in an
odd row `t` with the complementary even word `t+(1,1,1)`.  Every supported
even word is then `t+e_j` for exactly one `j`.  For coordinate `k`, two of
these three words agree with `t_k` and one disagrees.  Squared conference
coefficients are all `1/3`, proving `(CSM1)`.  The even and odd joint-label
sets are disjoint, proving the multiplicity obstruction.
