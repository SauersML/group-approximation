---
rg: 2
id: depth-three-r5-selector-proof
kind: route
title: Compare the two conjugate three-cycle characters
target: depth-three-r5-selector-pays-a6-label-flip
requires: []
---

Two transpositions with disjoint support commute.  Two transpositions with
one common letter generate `S_3`, and their commutator is a three-cycle.
This proves `(RSE2)`.  Direct multiplication likewise shows that
`c_i^(-1)c_j` is a three-cycle.  All three-cycles are conjugate in the
six-letter symmetric group.  Since the normalized character of any unitary
representation is constant on conjugacy classes,

```text
Re tr(pi(c_i^(-1)c_j))=Re tr(pi([s_j,z])).                       (RSP1)
```

For any unitary `u`,

```text
||u-I||_2^2=2-2 Re tr(u).
```

Use unitary invariance to replace `pi(c_i)-pi(c_j)` by
`I-pi(c_i^(-1)c_j)` and then apply `(RSP1)`, proving `(RSE3)`.

For the R5 assertion, refine one fixed complementary source cylinder so the
maximal prefix code containing

```text
000,010,10,110
```

has the same number of leaves as the depth-three code containing
`010,000,011,100`.  A prefix replacement can then send these four source
cylinders, in the displayed order, to the four target cylinders and match
the remaining fixed leaves arbitrarily.  Conjugation sends the two R5 swaps
to `s_i,z`, so it sends the R5 commutator relator to `[s_i,z]`.

