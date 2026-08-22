---
rg: 2
id: signed-three-face-rstar-petals-are-exact-cap-deletors
kind: claim
title: Signed three-face R-star petals delete arbitrary atoms but only by affine cap collapse
distinct_from:
  rstar-sunflower-neighborhoods-have-full-links: that proves one- and two-face fresh petals cannot delete anything; this classifies the first effective three-face geometry.
  rstar-fano-ghost-affine-hull-criterion: that characterizes cap supports abstractly; this gives an explicit fixed-language petal gadget realizing every desired deletion set.
  fano-cap-range-sections-cannot-encode-nonaffine-relations: that is a global pp-section no-go; this computes the exact local relation implemented by the proposed three-coordinate repair.
---

**ESTABLISHED EXACT THREE-FACE CALCULUS.**  Write

```text
R_*={x in F_2^4 : x_1+x_2+x_3+x_4=1}\{1000}.          (TFP1)
```

Let `c=(x_1,x_2,x_3,x_4)` be a center `R_*` context and fix any honest
assignment `b in R_*`.  Choose three distinct center coordinates `i,j,k`.
Define signed literals

```text
l_i=x_i+(1+b_i),   l_j=x_j+b_j,   l_k=x_k+b_k.          (TFP2)
```

Attach one fresh variable `y` and the petal

```text
R_*(l_i,l_j,l_k,y).                                     (TFP3)
```

Among center assignments in `R_*`, `(TFP3)` has an extension **except
exactly at `b`**.  Indeed, a triple `t` extends uniquely through its fourth
coordinate to the odd-parity hyperplane.  The extension is rejected only
when `t=100`, in which case the unique fourth coordinate is zero and the
tuple is the ghost.  By `(TFP2)`, the triple equals `100` exactly when a
center assignment agrees with `b` on `i,j,k`; two points of the same
odd-parity hyperplane agreeing on three coordinates agree on the fourth.

The signs require no language extension.  A complement wire is one
`R_*` row with a repeated dummy coordinate:

```text
R_*(d,d,x,xbar).                                        (TFP4)
```

Its parity equation is `x+xbar=1`, while its first two coordinates are
equal and hence can never be the ghost prefix `10`.  Thus `(TFP4)` enforces
`xbar=1+x` exactly.  Unsigned literals use `x` directly.

It follows that for every subset `B subseteq R_*`, a finite conjunction of
one signed three-face petal for each `b in B` has center projection exactly

```text
R_* \ B.                                                 (TFP5)
```

This gives a complete answer to the proposed three-coordinate repair.  It
can hit all seven translated Fano lines precisely when `B` is a blocking
set.  The survivor `R_*\B` is then a Fano cap, so

```text
Aff(R_*\B) subseteq R_*.                                (TFP6)
```

At the minimum size `|B|=3`, a blocking set in the Fano plane must itself
be a line.  Its four-point complement is a coset of the corresponding
two-dimensional subspace and is already an affine plane.  Therefore three
petals give an explicit maximal-cap branch, but no nonaffine behavior.

In particular, three-coordinate petals do **not** repair the CMPS compiler
while preserving all seven honest assignments.  They implement the same
affine-support choice already exposed by the Fano-profile route: any branch
that line-hits has deliberately discarded a blocking set.  Such a branch is
complete only when the chosen perfect model's center support is contained
in its surviving cap.  A model-selective or shared noncentral selection
mechanism remains necessary.

