---
rg: 2
id: mf-commensurability-from-radical-heredity
kind: route
title: Read commensurability invariance off the finite-index radical identity
target: mf-is-commensurability-invariant
requires: [corona-finite-index-radical-heredity]
artifacts:
  - GroupApproximation/Sofic/InducedCoronaMF.lean
---

## Why sufficient

A group is MF exactly when its MF radical is trivial and it is countable, so
the radical identity `Rad_MF(H) = H intersect Rad_MF(G)` decides both
directions at once.

Downward: `Rad_MF(G) = 1` forces `Rad_MF(H) = 1`.  (Directly: restrict a
faithful corona representation.)

Upward: if `Rad_MF(H) = 1` then `H intersect Rad_MF(G) = 1`.  For the
conclusion `Rad_MF(G) = 1` one needs slightly more than the identity, and the
induced representation supplies it: with `Theta` faithful on `H`, the induced
`Ind Theta` is faithful on `G`, because for `g in H` its `(1,1)`-block is
`Theta(g) != 1`, while for `g` outside `H` the permutation `sigma_g` moves the
first index, so the `(1,1)`-block is `0` and the block matrix is at operator
distance at least one from the identity.  This is
`InducedCoronaMF.isOperatorMF_of_finiteIndex_subgroup`.

Commensurability follows: two commensurable groups have isomorphic
finite-index subgroups, and the equivalence applies inside each.

## Priority

This half is already known in the MF literature (MF is closed under passage to
finite-index overgroups).  It is carded because the concrete
no-virtual-repair statements downstream cite it, not as a novelty claim.
