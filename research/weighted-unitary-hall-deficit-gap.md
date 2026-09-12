---
rg: 2
id: weighted-unitary-hall-deficit-gap
kind: claim
title: A weighted Hall deficit forces fixed Hilbert-Schmidt mass into forbidden unitary blocks
---

Let `P_i` and `Q_j` be two finite orthogonal decompositions of the identity in
`M_D(C)`, and let `U` be unitary.  Give the source and target vertices weights

```text
alpha_i=tr_D(P_i),
beta_j=tr_D(Q_j).
```

For subsets `S` of source vertices and `N` of target vertices put

```text
P_S=sum_(i in S) P_i,
Q_N=sum_(j in N) Q_j.
```

Then

```text
||(1-Q_N) U P_S||_2^2
 >= tr_D(P_S)-tr_D(Q_N).                              (HALL1)
```

In particular, suppose a bipartite support graph declares edges from `S` only
to `N(S)`, and all blocks on forbidden edges are `o(1)` in total squared
normalized Hilbert--Schmidt norm.  If the graph has a weighted Hall deficit

```text
sum_(i in S) alpha_i
 - sum_(j in N(S)) beta_j >= gamma > 0,               (HALL2)
```

then no such unitary sequence exists: forbidden-block energy is at least
`gamma`.

For a regular finite-group chart, taking the vertices to be the minimal
Wedderburn projections `e^sigma_aa` gives fixed rational weights
`d_sigma/|G|`, independent of external multiplicity.  Thus finite Fourier
compilation turns any relator-forced block-support pattern into a weighted
bipartite min-cut problem.  The singleton case is
`rectangular-wedderburn-block-isometry-gap`; the Hall form can succeed even
when no single target corner is too small.