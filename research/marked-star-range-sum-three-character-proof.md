---
rg: 2
id: marked-star-range-sum-three-character-proof
kind: route
title: Tensor the marked-star Pauli swaps with the three-character fold orbit
target: marked-star-range-sum-fold-retains-three-character-gauge
requires:
  - marked-star-outer-corrected-whiteheads-are-quarter-swaps
  - closed-compression-fold-loop-retains-s3-gauge
---

Let

```text
j=diag(1,-1,-1),
c_0=diag(-1,-1,1),              c_1=diag(-1,1,-1),
w_0=(0 2),                      w_1=(0 1).             (1)
```

Direct multiplication gives `c_0c_1=j`, while permutation of diagonal
entries gives

```text
w_0jw_0^(-1)=c_0,               w_1jw_1^(-1)=c_1.     (2)
```

The two transpositions are involutions and obey the adjacent braid.  Tensor
them with the two adjacent three-qubit swaps.  Tensor multiplication proves
the involution and braid rows in `(MSF4)`, equations `(2)` prove `(MSF2)`,
and the Pauli-factor swaps prove all marked-star covariances.

Every Pauli or qubit-swap label generator has determinant one.  The newly
adjoined fold signs and their chart permutations act on the second tensor
factor only.  Hence projection of every word to the eight-dimensional label
factor still has determinant one.  If that projection is an involution, its
negative multiplicity is even, excluding a rank-one reflection.

Finally the three nontrivial diagonal signs in `(1)` are conjugate under the
generated `S_3`, so every finite-dimensional representation assembled from
this three-character orbit gives them equal rank.  A trivial orbit adds the
same zero negative rank to each.  This proves the stated equal-source fence
for this occurrence table.
