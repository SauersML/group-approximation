---
rg: 2
id: no-magnus-hierarchy-sofic-via-coset-fold
kind: route
title: Fold the Magnus HNN extension through separating quotients with sofic coset actions
target: no-magnus-hierarchy-one-relator-groups-sofic
requires: [hnn-folds-into-free-coset-wreath, rigid-magnus-groups-have-sofic-separating-quotients]
artifacts:
  - research/artifacts/hnn-fold-free-coset-wreath-2026-09-11.md
---

A torsion-free two-generator one-relator group with zero-exponent basis is the
HNN extension of its Magnus piece `B_0` identifying `F_-` with `F_+` by the index
shift. This is the classical Magnus--Moldavanskii splitting (Lyndon--Schupp, IV.5),
equivalent to the kernel presentation used in the peeling artifact.

For a finite set `E`, fix reduced forms of `E^(-1)E \ {1}` and collect their
finitely many syllables. The second prerequisite gives `rho` into a sofic `H` with
a sofic coset action separating those syllables. The local form of the first
prerequisite makes the fold injective on `E`, with target a sofic free coset
wreath product. So `G` is sofic.
