---
rg: 2
id: balanced-schur-first-hit-placement-via-finite-depth-prefix
kind: route
title: Use explicit finite-depth prefix-preserving rows after the balanced child split
target: balanced-schur-reynolds-first-hit-placement
requires:
  - proper-corner-charged-section
  - relative-pauli-child-split-gives-one-exit-copy
  - hard-sign-transport-captures-exit-mass
  - finite-depth-prefix-preserving-hard-sign-hnn
  - balanced-schur-active-child-is-next-prefix-source
  - branching-plus-first-hit-exits-forces-hs-floor
---

The proper-corner cell orients the local split, and the Pauli theorem gives
one active plus one exit copy.  Hard-sign transport sends the exit to the
current negative pulse sector.  The finite-depth HNN rows preserve every
earlier positive pulse sign, so these exits lie in pairwise orthogonal
first-hit projections.  The active-incidence claim identifies the retained
child with the next prefix source and returns all inactive sectors.  These
are exactly the four estimates in `(BSR1)`; the branching ledger supplies
the final fixed-depth floor.

