---
rg: 2
id: non-hyperlinear-from-sl2-amalgamated-free-exclusion
kind: route
title: Excluding the amalgamated-free Haar unitary makes the Dogon--Vigdorovich HNN group the witness
target: non-hyperlinear-group
requires:
  - sl2-hnn-admits-no-amalgamated-free-haar-unitary
  - hnn-hyperlinearity-is-amalgamated-free-haar-unitary
---

By `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`, the finitely
presented group `G_2 = <SL_2(Z[1/2]), t | [t, SL_2(Z)] = 1>` is hyperlinear
iff some regular-trace matrix model of `SL_2(Z[1/2])` carries a Haar
unitary in the `SL_2(Z)`-centraliser free from the lattice factor with
amalgamation over `L(SL_2(Z))`; `sl2-hnn-admits-no-amalgamated-free-haar-unitary`
denies this, so `G_2` is the witness — the same group as in
`non-hyperlinear-from-hnn-over-sl2-z` and
`non-hyperlinear-from-relative-commutant-collapse`, reached from the
weakest hypothesis in that family.
