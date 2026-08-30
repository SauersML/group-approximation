---
rg: 2
id: stw84-common-stabilizer-wreath-bound
kind: claim
title: A split common infinite stabilizer preserves finite nuclear dimension of permutation wreath products
distinct_from:
  stw84-almost-free-permutation-wreath-bound: that requires every point stabilizer to be finite; here every stabilizer may contain the same infinite positive-rank subgroup.
  stw84-locally-finite-direct-factor-invariance: that adjoins a locally finite direct factor; the new direct factor is abelian of arbitrary finite rational rank and changes the quantitative bound.
  stw84-kernel-finite-locally-finite-by-abelian-computation: the shift part here can force a two-generated subgroup to meet the locally finite kernel infinitely.
artifacts:
  - research/artifacts/stw84-common-stabilizer-wreath-2026-08-30.md
---

Let `L` be a countable locally finite group.  Let `H` and `Q` be countable
abelian groups of finite rational ranks `h` and `q`, respectively.  Suppose
`Q` acts on a countable set `S` with finite point stabilizers, and let

`A=H direct_sum Q`

act on `S` through the quotient onto `Q`; thus `H` fixes every point.  Put

`G=(direct_sum_S L) rtimes A`.

If `q>=1`, then

`h+q <= dim_nuc(C*(G)) <= (h+1)(q+1)9^q-1`.             `(CSW1)`

If `q=0`, then the exact value is

`dim_nuc(C*(G))=h`.                                    `(CSW2)`

Every point stabilizer is

`A_s=H direct_sum Q_s`,

so it has rational rank exactly `h`.  In particular, this theorem genuinely
allows infinite stabilizers when `h>0`; their finite residual parts may
have unbounded orders.

For a concrete class outside both earlier action criteria, take

`H=Z`,  `Q=Z direct_sum (direct_sum_(n>=1) Z/2)`,

let `S` be the disjoint union of `Q/<e_n>`, and take `L=Z/2`.  Stabilizers
have rank one and are infinite, while the infinite cyclic translation
together with one lamp generates a subgroup meeting the lamp kernel
infinitely.  Nevertheless `(CSW1)` gives

`2 <= dim_nuc(C*(G)) <= 35`.
