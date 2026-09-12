---
rg: 2
id: factorial-leavitt-models-external-corner-commutant-proof
kind: route
title: Round the native corner heat, extract a central height, and kill it by factoriality
target: factorial-leavitt-models-have-external-corner-commutants
requires: [binary-leavitt-unit-group-has-tt-mod-t, binary-leavitt-elementary-group-is-simple, leavitt-gl-equals-el-and-perfect-unit-group]
artifacts:
  - research/artifacts/leavitt-heat-kernel-inclusion-and-cp-reversal-obstruction-2026-09-08.md
  - research/artifacts/leavitt-uniform-heat-rounding-alone-forces-nonhyperlinearity-2026-09-08.md
  - research/artifacts/leavitt-central-height-and-coordinate-swap-gap-2026-09-08.md
---

This is the second use in the audited two-use argument, stated for itself.
The steps are:
* the heat identification (8b);
* the equivalence (12) between 6.2(a) and uniform rounding;
* the balanced-flow central-height lemma for the native compressor;
* the generation identity (9), `H = <L, uKu^(-1)>`, with (12) in the
  exact ultraproduct. The finite-level swap ledger (11) is not needed.

* The (TT)/T input supplies property (T), hence the Kazhdan SOS certificate
  behind the heat estimates.
* Simplicity supplies ICC, and with it the infinite `L`-orbit of
  `x_14(a)` that makes the reverse defect tend to one.
* `GL = EL` supplies the elementary-matrix model of `H` on the rank-four cell.

The selection step of the two-use argument is not used. The contradiction
comes from factoriality of the global commutant itself.
