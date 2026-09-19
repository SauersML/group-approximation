---
rg: 2
id: stw22-colour-local-weighted-corner-lifts-proof
kind: route
title: Glue local weighted corner embeddings with d+1 colours and keep the range norm bounded
target: stw22-finite-dimensional-colouring-from-local-lifts
requires:
  - stw22-zero-dimensional-trivial-field-trace-continuity
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-finite-dimensional-coloured-selection-audit-2026-08-30.md
---

Put `R=pi_tau(U)''` and assume `(LWCL)` from the claim.  This is
deliberately stronger than the sequential lower-lifting property used in
the zero-dimensional argument.  Pointwise or sequential lower lifting of a
multifunction does not by itself produce an exact continuous local section
on a positive-dimensional neighbourhood.

We prove `(FDC)`.  Choose pairwise orthogonal projections
`e_1,...,e_m in R` with `tau(e_j)=1/m`.  The strict inequality in `(FDS)`
and `(LWCL)` give a finite open cover of `V` on each member of which, for
every `j`, there is a weighted lift `w_(j,alpha)` of `c` with range support
below `e_j`.

By the covering-dimension refinement theorem, refine this cover to a finite
open cover which is the union of `d+1` families, each family pairwise
discrete, and choose a partition of unity `(f_alpha)` subordinate to it.
Shrink the refinement so that supports belonging to one colour are
pairwise disjoint.  For `0<=r<=d`, set

```text
v_(j,r)=sum_(colour(alpha)=r) f_alpha^(1/2) w_(j,alpha).
```

The sums are continuous sections because within one colour the scalar
supports are disjoint.  Cross terms within a colour vanish, and hence

```text
v_(j,r)^*v_(j,r)
  =sum_(colour(alpha)=r) f_alpha c.
```

Summing over `r` gives the first part of `(FDC)`.  For fixed `j,r`, the
range support lies below `e_j` and the section is contractive.  At each
base point there is at most one active member of a given colour, so

```text
sum_(r=0)^d v_(j,r)v_(j,r)^* <= (d+1)e_j.
```

The `e_j` are orthogonal; summing over `j` proves the norm bound in `(FDC)`.

Now let `a in K_x/J_x` be a positive contraction and fix `epsilon>0`.
For `c=(a-epsilon)_+`, Chebyshev and `2`-norm continuity at `x` give, for
every chosen `m`, a neighbourhood on which `(FDS)` holds.  A scalar cutoff
allows us to take `V` open with compact support; the part outside `V`
vanishes in `J_x`.  Applying `(FDC)` and traciality gives `(FDT)`.  Let
`m -> infinity`, then `epsilon -> 0`, to conclude that every bounded trace
on the gap is zero.  The abstract fibre-gap criterion finishes the proof
under `(LWCL)`.
