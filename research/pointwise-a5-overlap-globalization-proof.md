---
rg: 2
id: pointwise-a5-overlap-globalization-proof
kind: route
title: Use the diameter-two context graph and telescope each Carmichael word
target: pointwise-a5-overlap-globalizes-carmichael-family
requires: []
---

Fix `i`.  The triples containing `i` are indexed by the two-subsets of
`[M] setminus {i}`.  Two such triples share two indices exactly when the
corresponding vertices are adjacent in the Johnson graph `J(M-1,2)`.  This
graph has diameter at most two: two disjoint two-subsets are joined through
any two-subset containing one point from each.  The cases `M=3,4` have
diameter zero and one respectively.

Choose one reference triple `T_i` containing each `i` and put

```text
X_i=Y_i^(T_i).
```

By `(POG2)` and a path of length at most two,

```text
||X_i-Y_i^T||_2 <= 2 epsilon                            (PGP1)
```

for every triple `T` containing `i`.  Each `X_i` remains a literal conjugate
of `B`, and `(POG1)` on its reference chart gives the cube estimate.

For `i!=j`, choose `k` distinct from both and put `T={i,j,k}`.  Telescoping
the four unitary factors and using unitary invariance of normalized
Hilbert--Schmidt norm gives

```text
||(X_iX_j)^2-(Y_i^T Y_j^T)^2||_2
 <= 2||X_i-Y_i^T||_2+2||X_j-Y_j^T||_2
 <= 8 epsilon.                                         (PGP2)
```

Combining `(PGP2)` with the local pair estimate in `(POG1)` proves `(POG3)`.

