---
rg: 2
id: rank-two-weyl-triangle-gauge-detector-proof
kind: route
title: Put the one-direction corrector on two tensor factors and evaluate the three-term diagonal word
target: rank-two-weyl-triangle-is-first-apartment-gauge-detector
requires: []
---

Take the regular finite coefficient representation with a two-dimensional
spectator, place identical copies on `E tensor E`, and let the corrector be
the tensor flip.  The flip commutes with the diagonal coefficient action, so
`rho(g)Z` implements exactly the same inner automorphism as `rho(g)`.  It
sends the half projection on the first spectator to the half projection on
the second spectator.  Those projections commute and have intersection
trace `1/4`.

For the three Weyl-conjugate diagonal directions, a corrector in the full
coefficient commutant is unchanged by Weyl conjugation.  Writing the lifts as
`GZ,G'Z,G''Z`, the diagonal identity `G(G'')^-1=G'` cancels both copies of
`Z` on the left while leaving one on the right.  The lifted relation is
therefore equivalent to `Z=1`.  This both proves collapse in the common-slot
sector and shows, by the tensor flip, that deleting this rank-two word restores
an exact interior-overlap model.
