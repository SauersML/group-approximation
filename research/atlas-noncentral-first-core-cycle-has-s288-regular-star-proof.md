---
rg: 2
id: atlas-noncentral-first-core-cycle-has-s288-regular-star-proof
kind: route
title: Attach the S3-square and collision S4 to the order-96 core by regular actions
target: atlas-noncentral-first-core-cycle-has-s288-regular-star
requires:
  - atlas-forward-core-triangle-has-faithful-q96-completion
---

The exact finite core has

```text
|Q|=96,       <c,u>~=V4,       <c,t>~=A4.            (STAR-1)
```

The desired oververtices have

```text
F'=S3 x S3,   |F'|=36,         <c,u>~=V4,
J=S4,         |J|=24,          <c,t>~=A4.             (STAR-2)
```

Take three copies of `Reg(Q)`, eight copies of `Reg(F')`, and twelve copies of
`Reg(J)`.  All three actions have degree 288.  On the first overlap,

```text
3 Reg(Q)|_V4 =3*24 Reg(V4)=72 Reg(V4),
8 Reg(F')|_V4=8*9 Reg(V4)=72 Reg(V4).                 (STAR-3)
```

On the second overlap,

```text
3 Reg(Q)|_A4 =3*8 Reg(A4)=24 Reg(A4),
12 Reg(J)|_A4=12*2 Reg(A4)=24 Reg(A4).                (STAR-4)
```

Choose permutation conjugacies realizing these two labeled identifications.
Both finite oververtices and `Q` remain faithful in the generated subgroup of
`S_288`.  Since the common `Q` action fixes the labels shared by the two
overlaps, the two alignments are simultaneous.  This gives the asserted
noncentral collision/first-core carrier.

The construction leaves one explicitly isolated cycle.  The 144-state fan
vertex `C` must meet `F'` in `A=<r,z>` of order nine and meet `J` in
`B=<b>` of order two.  Attaching `C` over either edge is another regular tree
amalgam; imposing the other identification is the first remaining
double-coset/vertex-injection problem.
