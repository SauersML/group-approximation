---
rg: 2
id: steinberg-flag-fox-map-is-injective
kind: claim
title: The authenticated flag-incidence Fox map is injective in every odd defining characteristic
---

For every odd prime `p`, the map `D_p` of
`steinberg-fox-kernel-is-flag-incidence` is injective.

Equivalently, a coefficient function on the flags of `F_p^3` which has zero
sum on every point panel and every plane panel, and which satisfies both
finite-difference equations in `(SFI2)`, is zero.

This is the exact unresolved Steinberg-module lemma.  No apartment-sign or
Weyl-character argument proves it, because the coefficient transformations
do not preserve the standard apartment.  A proof must retain the root-group
coordinates in the flag incidence system; a nonzero solution would instead
be an explicit defining-characteristic affine-gauge counterexample.

The first prime instance is now closed without any marginal assumption:
`steinberg-flag-fox-map-is-injective-at-p-three` eliminates all nine chord
fibers by an exact characteristic-three `X,Y` cascade.  The present claim
remains open because the authenticated mixed-loop argument requires the
same injectivity uniformly for every odd prime.

The established node `steinberg-cycles-have-big-cell-chord-coordinates`
removes all panel variables: the claim is now equivalent to the two
three-variable equations `(SBC5)`, whose exceptional transformed flags are
fixed signed cut-sums in one explicit spanning tree.
