---
rg: 2
id: invariant-graph-ce-route
kind: route
title: Detect the sofic-radical sign in any nondegenerate invariant-graph model
target: hyperlinear-nonsofic-group
requires: [invariant-graph-clifford-phase, invariant-graph-crossed-product-ce]
artifacts:
  - notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md
---

## Why sufficient

Take the invariant graph `S` supplied by the embeddability claim.  The
classification claim gives a surjection `H ->> Wtilde_S` sending the
Kun--Thom radical word `x` to `z`, a faithful embedding
`Wtilde_S <= U(M_S)` with `z |-> -1`, and nonsoficity of `Wtilde_S`.  The
group `Wtilde_S` is countable.  If `M_S` is Connes embeddable then
`Wtilde_S <= U(M_S) <= U(R^U)`, so `Wtilde_S` is hyperlinear.  A hyperlinear
group that is not sofic is exactly the program target.

This route is strictly weaker than `kun-thom-clifford-ce-route`: that one
needs the complete-graph algebra `Cl(G/Gamma) crossed_product G`, which is
the `S`-complete instance of the family here, and any *one* member suffices.
