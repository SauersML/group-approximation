---
rg: 2
id: atlas-o8m2-a8-pairs-have-five-normalizer-cells
kind: claim
title: O8-(2) A8 pairs have five normalizer cells and three genuine cross-carrier cells
artifacts:
  - experiments/atlas_o8m2_a8_pair_cells.py
  - experiments/atlas-o8m2-a8-pair-cells.json
distinct_from:
  atlas-o8m2-has-one-a8-class-with-c3-centralizer: that classifies individual A8 subgroups; this classifies ordered pairs and isolates the cells not covered by an Sp6 carrier.
---

Let `G=O8-(2)`, let `A~=A8`, and put `N=N_G(A)~=(3 x A8):2`.
The five cells of `N\G/N`, equivalently the five point-stabilizer orbits in
the degree-`1632` action on `A^G`, have the following exact data:

```text
subdegree  |N intersect N^g|  |A intersect A^g|  <A,A^g>       common Sp6
     1          120960             20160         A8                 3
    56            2160                60         O8-(2)             0
   105            1152               576         Sp6(2)             1
   630             192                32         O8-(2)             0
   840             144                36         O8-(2)             0. (OMP1)
```

The intersection structures down the rows are respectively

```text
A8, A5, ((A4 x A4):C2):C2, (C2^3):(C2^2), S3 x S3.
```

Thus the identity and `105` cells are exactly the pairs sharing an `Sp6(2)`
carrier.  The existing `Sp6(2)` packet screen absorbs the nontrivial one.
The only genuinely new pair cells have subdegrees `56,630,840`, and every
one generates the full ambient simple group.  Since `N/C_G(A)~=S8`, no
additional relative graph-parity split is required.

