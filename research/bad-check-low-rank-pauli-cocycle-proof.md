---
rg: 2
id: bad-check-low-rank-pauli-cocycle-proof
kind: route
title: Tile by complete bipartite commutation blocks and count rank and vertex-cover cost
target: bad-check-nullity-does-not-exclude-far-pauli-cocycles
requires: []
---

Put `k=ceil(1/eta_L)` and, after discarding fewer than `2k` harmless
coordinates, partition the coordinates into `k` equal blocks of even size
`s=Theta(L/k)`.  Split each block into two halves and let its commutation
graph be the complete bipartite graph `K_(s/2,s/2)`, with no edges between
blocks.  The alternating adjacency matrix of one block is

```text
[ 0  J ]
[ J' 0 ],                                                 (BCP1)
```

where `J` is the all-ones matrix, so it has binary rank two.  Hence the
whole alternating matrix has rank `2k=O(1/eta_L)`.  Its number of ordered
ones is

```text
k * 2(s/2)^2 = L^2/(2k)=Theta(eta_L L^2),                 (BCP2)
```

which proves `(BCN1)`.  Every alternating binary matrix is the Gram matrix
of vectors in a binary symplectic space of dimension its rank, so the usual
Weyl representation realizes `(BCN2)` by reflections in matrix dimension
`2^(rank(B_L)/2)`.

Let `(P_i)` be commuting reflections and put
`e_i=||Q_i-P_i||_2^2`.  On every edge, telescoping the commutator and using
that `Q_i,Q_j` anticommute while `P_i,P_j` commute gives

```text
e_i+e_j >= c_0                                             (BCP3)
```

for a numerical `c_0>0`.  Sum over the edges of one bipartite block.  Every
vertex has degree `s/2`, so `(BCP3)` gives

```text
(s/2)sum_(i in block)e_i >= c_0 s^2/4,
sum_(i in block)e_i >= c_0 s/2.                           (BCP4)
```

Summing the blocks proves a constant lower bound for
`L^(-1)sum_i e_i`.

Finally `eta_L^2L->infinity` implies

```text
rank(B_L)=O(1/eta_L)=o(eta_L L).                          (BCP5)
```

Deleting `eta_L L` independent rows from a parity matrix can enlarge its
kernel quotient by as much as `eta_L L`, so dimension alone cannot exclude
the cocycle just constructed.

