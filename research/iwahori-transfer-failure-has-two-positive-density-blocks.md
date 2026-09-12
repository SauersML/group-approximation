---
rg: 2
id: iwahori-transfer-failure-has-two-positive-density-blocks
kind: claim
title: A failed Iwahori projection transfer has two positive-density blocks
distinct_from:
  iwahori-outlier-repair: that warns a sparse operator subspace may contain a full-rank invertible element; this proves that a projection witnessing the weaker transfer failure must itself split the Hilbert space into two linearly large blocks.
  iwahori-transfer-failure-reduces-to-two-block-projection: that produces the projection normal form; this derives the quantitative rank density forced by its nonvanishing second-vertex commutator.
---

Let `P` be a projection and `U` a unitary in `M_d`.  Then

```text
||[P,U]||_2^2
 =||P-UPU^*||_2^2
 <=2 min(tr_d(P),1-tr_d(P)).                         (PDB1)
```

Indeed `P` and `UPU^*` are equal-trace projections, and

```text
||P-UPU^*||_2^2
   =2tr_d(P)-2tr_d(PUPU^*)
   <=2tr_d(P).                                       (PDB2)
```

Applying the same calculation to `1-P` gives the other bound.

Consequently, in every counterexample sequence `(TBP1)--(TBP2)` from
`iwahori-transfer-failure-reduces-to-two-block-projection`, after choosing
one second-vertex generator whose commutator is at least `epsilon_0`,

```text
tr(P_d)>=epsilon_0^2/2,
1-tr(P_d)>=epsilon_0^2/2.                            (PDB3)
```

Thus the two asymptotic reducing blocks both have positive Hilbert-space
density.  A failed transfer cannot be supported on `o(d)` physical rank,
even though its witness is only one vector in the `d^2`-dimensional adjoint
space.
