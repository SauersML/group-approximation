---
rg: 2
id: sl3-double-quasiregular-tensor-is-a-uniform-outlier
kind: claim
title: The quasi-regular tensor assignment of every canonical SL3 double enemy is uniformly far from exact representations
distinct_from:
  sl3-double-tensor-leak-is-quasiregular: that identifies the limiting pointed representation and shows tensor amplification preserves it; this converts that pointed coefficient into a dimension-free distance from the exact finite-dimensional representation variety.
  sl3-double-one-near-vertex-forces-joint-near-exactness: that corrects the second vertex after one factor is anchored; this excludes correction of the tensor product even when neither tensor factor is correctable.
  sl3-canonical-double-has-a-correctable-vertex: that asks to correct at least one tensor factor; this proves the weaker but unconditional fact that the paired tensor assignment itself cannot be corrected.
---

Let `pi_(n,0),pi_(n,1)` be the vertex restrictions of any canonical-trace
microstate sequence of

```text
D=A *_C A,       A=SL_3(Z[1/2]),       C=SL_3(Z),
```

and put

```text
rho_n(a)=pi_(n,0)(a) tensor conjugate(pi_(n,1)(a)).             (QTO1)
```

For a fixed finite generating set `S_A`, there is `epsilon_0>0`, depending
only on the arithmetic pair and the presentation words, such that

```text
inf_(alpha:A->U(d_n^2) exact)
  max_(s in S_A)||rho_n(s)-alpha(s)||_2 >= epsilon_0            (QTO2)
```

for all sufficiently large `n`.  The same conclusion holds for every fixed positive tensor power of
`rho_n`, with a constant allowed to depend on the power.

Thus simultaneous two-vertex outliers cannot cancel each other's defects
inside the obvious diagonal tensor representation.  A matrix-coordinate
correction theorem for the tensor witness would refute the canonical double
enemy outright; it would not extract a correctable factor.
