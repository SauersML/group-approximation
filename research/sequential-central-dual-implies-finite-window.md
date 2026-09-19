---
rg: 2
id: sequential-central-dual-implies-finite-window
kind: route
title: Diagonalize failures of all finite separator windows into one canonical HNN outlier
target: sl3-hnn-finite-window-central-dual-gap
requires:
  - sl3-hnn-central-dual-gap-vanishes
---

Argue contrapositively.  If the finite-window claim fails, there are fixed
`M<infinity` and `epsilon>0` such that every pair `(W,delta)` admits a
dimension, a unitary presentation assignment `x`, and a tuple `B` satisfying
`(FDG1)--(FDG2)` while the gap in `(FDG3)` is greater than `epsilon`.

Enumerate the nonidentity elements of the countable group `G_p` as
`g_1,g_2,...`.  At stage `n`, take

```text
W_n={g_1,...,g_n},       delta_n=1/n,
```

and choose a violating pair `(x_n,B_n)`.  The defining relators have defect
tending to zero.  Every fixed equality of group words has a finite van
Kampen derivation from the fixed presentation, so word evaluation is
asymptotically multiplicative.  For each nonidentity `g_i`, its normalized
trace tends to zero once `n>=i`.  Thus `(x_n)` is a canonical hyperlinear
approximation of `G_p`.  The tuples `B_n` are normalized, uniformly bounded
by `M`, asymptotically central under the stable letter, and retain separation
gap greater than `epsilon`.  This contradicts `(LCG3)` and proves the finite
window claim.
