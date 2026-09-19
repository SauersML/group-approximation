---
rg: 2
id: repeated-ldpc-weyl-approximate-rank-proof
kind: route
title: Decode low-rank columns against the repeated code distance
target: repeated-ldpc-weyl-kernel-has-growing-approximate-rank
requires:
  - bounded-prefix-decision-cost-forces-bounded-approximate-rank
  - repeated-good-ldpc-coordinates-give-private-weyl-sampler
---

Choose one original coordinate representative for each of the `q` distinct
vectors in the list `B`, and retain all `R` repeats of each representative.
The corresponding `qR` columns of `K` are repeated copies of `q` distinct
codewords of `(LRK1)`.  After row repetition, any two of those codewords
still have Hamming distance at least `delta N`.

The columns of a rank-`k` Boolean matrix take at most `2^k` distinct values.
Call one of the selected columns good if its distance from the corresponding
column of `K` is strictly below `delta N/2`.  By code distance, one fixed
column value of `K'` can be good for at most one of the `q` distinct true
codewords, hence for at most its `R` repeated columns.  Therefore at most
`R 2^k` selected columns are good.  Every other selected column contributes
at least `delta N/2` changed entries.  Hence

```text
dist_H(K,K')
 >= R(q-2^k) delta N/2,
```

which is `(LRK3)` after division by `N^2=(LR)^2`.  Since `q>=r` and
`L<=Cr`, the assumed error bound gives `2^k>=r/2`, proving `(LRK4)`.

For the prefix consequence, truncate a procedure of expected depth `D` at
depth `m`.  As in the established bounded-prefix theorem, the truncated
matrix has rank at most `2^m` and differs on at most `D/m` of the entries.
Fix an error rate below `delta/(4C)` and take `m=O(D)`.  Equation `(LRK4)`
forces

```text
2^m >= log_2(r)-1,
```

so `D=Omega(log log r)`.  The second-moment truncation uses
`Pr(depth>m)<=E(depth^2)/m^2` and gives `(LRK6)`.
