---
rg: 2
id: atlas-full-c144-relation-forces-nonsolvable-q1920-kernel
kind: claim
title: The full C144 relation forces every faithful Q1920 completion to have nonsolvable seam kernel
distinct_from:
  atlas-full-large-finite-escape-has-simple-local-factor: that passes an arbitrary faithful finite completion to a simple quotient and audits the four finite vertex kernels; this directly eliminates every completion whose reduced-seam kernel is solvable.
  atlas-q1920-solvable-kernel-forces-small-f3-chief-factor: that analyzes possible chief factors before imposing the second C144 fan relation; this shows that relation makes the entire solvable-kernel branch impossible.
  atlas-q1920-dim10-f3-reduced-seam-has-affine-signal: that constructs a large finite solvable-kernel completion of the reduced seam; this explains dimension-independently why it cannot extend to C144.
---

Let `P=N semidirect A5` be the reduced universal seam from
`atlas-q1920-universal-seam-splits-over-a5`, let `V=C2^5` be the unique
normal binary module in the marked `Q=Q1920`, and impose the remaining
forward-fan relator

```text
(z b)^3=1.                                                (Q1920-C144-1)
```

Suppose a quotient `G` of this full presentation is injective on `Q`, and
write `K` for the image of `N`.  The reduced-seam calculation gives
`V,z <= K`.  Consequently `K cap Q` is a normal subgroup of `Q` containing
`V`.  The exact normal-subgroup lattice of `Q=2^5:A5` has only two such
possibilities:

```text
K cap Q = V  or  Q.                                      (Q1920-C144-2)
```

If `K` were solvable then it could not contain the nonsolvable group `Q`, so
`K cap Q=V`.  In particular the marked involution `b` has order two in
`G/K`, because `b` is not in `V`.  But `z` lies in `K`, and projecting
`(Q1920-C144-1)` to `G/K` gives

```text
1=(z b)^3 K=(bK)^3=bK,
```

a contradiction.  Therefore

```text
Q injects in G  ==>  image_G(N) is nonsolvable.           (Q1920-C144-3)
```

This is independent of dimension and finiteness of `G`; only solvability of
the image of `N` is used.  It closes all affine and solvable-chief-factor
extensions at once.  Any surviving finite carrier must put a nonabelian
simple chief factor inside the moved seam kernel itself.

## Attempts

The characteristic-three polynomial program finds an exact ten-dimensional
affine completion before `(z b)^3`, but its forward subgroup has order 324.
Equation `(Q1920-C144-3)` shows that no larger solvable radical or additional
derived layers can repair it.  The remaining attack is necessarily on a
nonsolvable moved-kernel completion, not on further modules over `F3`.
