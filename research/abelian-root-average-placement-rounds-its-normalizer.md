---
rg: 2
id: abelian-root-average-placement-rounds-its-normalizer
kind: claim
title: Average placement of a regular abelian root table rounds the optimal atom normalizer
artifacts:
  - research/artifacts/parallel-group-word-2026-09-04.md
distinct_from:
  two-pauli-anchors-localize-arbitrary-normalizer-twists: that localizes one matrix to a Pauli commutant; this rounds an arbitrary unitary to the normalizer of a commutative root algebra while choosing its atom matching.
---

Let `H` be a finite abelian group of order `q`, represented as `m` copies
of its regular representation on `C^(qm)`. Its character projections `P_x`
all have rank `m`. Put

```text
A=span{P_x},     U_h=sum_x x(h)P_x,
L(V)=avg_(h in H)||VU_hV^*-E_A(VU_hV^*)||_2^2,
```

where `E_A` is normalized-trace-preserving conditional expectation and
`V` is any unitary. Then

```text
dist_2(V,N(A))^2 <= 2L(V).                              (ARP1)
```

The normalizer permits arbitrary permutations of the atoms and arbitrary
unitaries between matched rank-`m` blocks. The constant is independent of
both `q` and `m`; the matching is chosen after `V` is given.

More explicitly, the doubly stochastic matrix

```text
B_(x,y)=||P_x V P_y||_F^2/m
```

satisfies

```text
L(V)=1-q^(-1)sum_(x,y)B_(x,y)^2.                       (ARP2)
```

Thus full-table placement loss is a sufficient quantitative interface for
joint-atom return. The linked artifact constructs exact canonical root
tables for which every bounded-support covariance test tends to zero but
`L(V)->1` and `dist_2(V,N(A))->sqrt(2)`. No dimension-independent replacement
of this full-table average by arbitrary local root tests is asserted.

DERIVATION
abelian-root-placement-birkhoff-polar-proof
