---
rg: 2
id: fournier-facio-purely-singular-near-proof
kind: route
title: Apply the near-representation criterion and eliminate the normal state component
target: fournier-facio-hyperlinear-iff-singular-near
requires:
  - hyperlinear-near-representation-criterion
  - map-free-near-state-is-purely-singular
  - fournier-facio-group-is-minimally-almost-periodic
---

If `G` is hyperlinear, the Kahl--Schneider criterion supplies a Hilbert
space, an invariant state and a near representation inducing the regular
character.  Since `G` is nontrivial and minimally almost periodic,
`map-free-near-state-is-purely-singular` forces the normal component of that
state to vanish.

Conversely, clause 2 of the target is precisely the state form of the
Kahl--Schneider hyperlinearity criterion, with the additional restriction
that the state is purely singular.  Forgetting that restriction proves that
`G` is hyperlinear.

