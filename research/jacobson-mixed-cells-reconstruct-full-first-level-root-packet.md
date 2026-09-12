---
rg: 2
id: jacobson-mixed-cells-reconstruct-full-first-level-root-packet
kind: claim
title: The Jacobson TS cell and first braid reconstruct the full nine-coordinate root packet
distinct_from:
  jacobson-boundary-cell-reconstructs-finite-root-packet: that reconstructs a six-coordinate root packet containing the shifted operator; this uses the two remaining mixed cells to reconstruct nine root coordinates and a finite subgroup containing the entire original packet.
artifacts:
  - research/artifacts/jacobson-ts-splitting-and-first-level-root-packet-2026-09-08.md
---

Use the exact finite groups and their specified intersection from
`jacobson-boundary-cell-reconstructs-finite-root-packet`, and define

```text
Xi=< F *_(P_Q x K_P) J | (h b)^3=1, W=1 >,
F=GL_3(F_2)_Q x GL_3(F_2)_P,
J=Hom(F_2^2,F_2^3) semidirect (K_Q x G_*).
```

Put `a_1=x_21,Q`, `a_2=x_23,Q`, `a_3=a_1 a_2`,
`r=x_23,P`, `D_i=h a_i h`, and `u=[h x_13,P h,x_31,P]`.
The TS cell splits into the exact relations

```text
[r,D_i]=1 for all i,             [u,h r h]=r.
```

For exact finite packets and TS error `w=||W-I||`, their respective
errors are at most `2w` and `3w`. The first braid additionally
makes `D_1` commute with the full tail stabilizer of `e_1` and the
full head stabilizer of `e_1^*`.

Consequently the `F`-conjugates `D(v,f)` are well-defined for nonzero
tail vectors and head covectors. They are additive in both arguments
and all commute. Their group is the embedded additive matrix space
`Mat_(3 x 3)(F_2)`. Together with `F` they form the finite subgroup

```text
Mat_(3 x 3)(F_2)_add semidirect F,
X |-> g_P X g_Q^(-1),
of order 14,450,688.
```

Injectivity follows from the literal level-zero to level-one action.
The head mark survives in `Xi`. This finite subgroup does not contain
`h`; its reconstruction alone establishes no coherent matrix
correction, opposite-root closure, or positive matrix gap.

DERIVATION
jacobson-ts-split-bilinear-root-proof
