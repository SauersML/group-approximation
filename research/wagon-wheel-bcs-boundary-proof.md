---
rg: 2
id: wagon-wheel-bcs-boundary-proof
kind: route
title: Separate the fixed-area word estimate from the affine scalar boundary of every local LCS fragment
target: wagon-wheel-stops-before-bcs-groupification
requires:
  - slofstra-solution-group-embedding-preserves-marked-involutions
  - marked-approximate-radical-survives-solution-group-embedding
  - mipstar-bcs-tracial-nonru-exists
  - paddock-slofstra-bcs-forbidden-projection-dictionary
  - locally-affine-support-bcs-is-exactly-the-lcs-boundary
  - wagon-wheel-exact-radical-has-hs-wall
---

If a word is a product of `A` conjugates of defining relators, unitary
invariance of normalized Hilbert--Schmidt norm and the telescoping inequality
give `(WW2)`.  Apply this to the finitely many displayed source-relator
fillings and the fixed marked equality in Slofstra's construction.

Assuming `(WW3)--(WW4)`, any separated approximate model sequence yields a
nonzero ultraproduct corner.  The forbidden-projection dictionary turns
`V_B->0` into exact vanishing of every forbidden atom there, while the
structural defect gives one shared BCS tuple.  This contradicts the imported
non-`R^U` BCS.  Thus the mark is approximately radical, and fixed-word
restriction through the wagon wheel transfers that fact.

Finally, scalar solutions of a finite LCS with `J=-1` are solutions of an
affine system over `F_2`.  Coordinate projection preserves affineness.  Exact
completeness and soundness therefore force the visible allowed set to be
affine; otherwise an affine-hull ghost is an exact zero-defect forbidden
model.  Replacing the whole allowed set by the support of one trace gives
exactly `(WW6)`, the locally affine-support boundary.  These three elementary
steps prove the claim.

The exact-radical firewall is independent and sharp. The motivating output
sign is zero in every exact finite-dimensional representation, but the
permutation tuples in `wagon-wheel-exact-radical-has-hs-wall` have defect
tending to zero and keep it at distance `sqrt(2)`. Therefore neither exact
finite-dimensional invisibility nor bounded wagon area supplies the missing
estimate `(WW3)`.
