---
rg: 2
id: typewise-tail-partition-via-matrix-only-atom-selection
kind: route
title: Feed matrix-selected Reynolds atoms through the orthogonal pair-HNN router
target: typewise-schur-tail-partition-compiler
requires:
  - shared-bcs-matrix-only-supercritical-atom-selection
  - central-sign-assignment-atom-is-index-two-reynolds-surplus
  - index-two-reynolds-atoms-have-orthogonal-hnn-transports
  - partitioned-child-surplus-collision-supplies-contraction
  - non-ce-bcs-has-robust-approximate-energy-gap
  - finite-schur-clifford-packet-flexible-hs-exactification
  - free-cone-shift-finitely-wordizes-recursive-clifford-tails
  - bounded-overlap-syndrome-energy-accounting
---

The selection theorem supplies `(SAM1)--(SAM2)` on one shared BCS tuple.
Interpret its assignment atoms as index-two Reynolds differences.  Pad the
marked pairs to one fixed elementary-abelian rank and apply the pair-HNN
router, choosing distinct target characters inside the next recursive-tail
packet.  The target projections are pairwise orthogonal, and `(ITH5)` plus
bounded-overlap accounting gives `(TSP2)` with polynomial addressed cost.

The perfect zero-violation completion supplied by the selection theorem and
the free-cone tail gives clause 3 of the target.  Hence all clauses of
`typewise-schur-tail-partition-compiler` follow.

