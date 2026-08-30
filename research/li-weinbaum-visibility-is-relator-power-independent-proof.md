---
rg: 2
id: li-weinbaum-visibility-is-relator-power-independent-proof
kind: route
title: Kill the primitive root in every locally indicable target
target: li-weinbaum-visibility-is-relator-power-independent
requires: []
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

A locally indicable group is torsion-free.  Indeed, a nontrivial finite cyclic
subgroup is finitely generated but cannot map onto `Z`.

Let `psi:G_m->Q`, where `Q` is locally indicable.  The defining relation gives
`psi(v)^m=1`, so torsion-freeness gives `psi(v)=1`.  Hence `psi` factors
uniquely through `p_m:G_m->G_1`.  Conversely every homomorphism from `G_1`
precomposes with `p_m`, proving the asserted bijection.  Both corresponding
maps take the same value on every word in `F`, so nontriviality on any fixed
packet is preserved in both directions.
