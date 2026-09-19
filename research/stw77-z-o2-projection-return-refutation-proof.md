---
rg: 2
id: stw77-z-o2-projection-return-refutation-proof
kind: route
title: Combine O2 absorption with the projectionless-range obstruction
target: stw77-z-o2-map-defeats-projection-return
requires:
  - projectionless-ranges-obstruct-projection-return
---

## Proof

The standard absorption isomorphism `O_2 tensor Z ~= O_2` gives a unital
embedding `phi:Z->O_2` from the second tensor factor.  Its range is a
nontrivial unital projectionless algebra.  Therefore
`projectionless-ranges-obstruct-projection-return` shows that `phi` cannot
satisfy the proposed projection-return selection property.

Every nonzero positive element of `O_2` is properly infinite because `O_2`
is simple and purely infinite, so the image hypothesis holds.  The map is
nuclear (its domain is nuclear), full (it is unital and `O_2` is simple),
and O2-stable: a central sequence copy witnessing O2-absorption of the
codomain commutes with all of `O_2`, hence with `phi(Z)`.  The theorem that
full nuclear O2-stable maps with separable exact domain have nuclear
dimension zero now applies.

Finally, O2-stability supplies a unital copy of `O_2`, and hence of
`O_infinity`, in the map-relative central sequence algebra.  Thus this map
is positive evidence for LXXVII while being a rigorous refutation of the
projection-return proof strategy.
