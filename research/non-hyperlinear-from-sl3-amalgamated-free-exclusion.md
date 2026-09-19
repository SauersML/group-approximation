---
rg: 2
id: non-hyperlinear-from-sl3-amalgamated-free-exclusion
kind: route
title: Excluding the amalgamated-free Haar unitary makes the rank-two HNN group the witness
target: non-hyperlinear-group
requires:
  - sl3-hnn-admits-no-amalgamated-free-haar-unitary
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
---

`hnn-hyperlinearity-is-amalgamated-free-haar-unitary` says the finitely
presented group `G_3 = <SL_3(Z[1/2]), t | [t, SL_3(Z)] = 1>` is hyperlinear
iff some regular-trace matrix model of `SL_3(Z[1/2])` carries a Haar
unitary in the `SL_3(Z)`-centraliser free from the lattice factor with
amalgamation over `L(SL_3(Z))`.  `sl3-hnn-admits-no-amalgamated-free-haar-unitary`
denies this for every model, so `G_3` is not hyperlinear and is the
explicit witness.  This is the same witness as
`non-hyperlinear-from-sl3-relative-commutant-collapse`, reached from a
strictly weaker hypothesis.
