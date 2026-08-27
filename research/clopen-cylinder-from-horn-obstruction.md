---
rg: 2
id: clopen-cylinder-from-horn-obstruction
kind: route
title: Turn the finite Horn obstruction into a marked-group cylinder
target: clopen-non-mf-cylinder
requires: [mf-universal-horn-obstruction]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralMarkedCylinder.lean
---

## Why sufficient

Finitely many word equations and one inequation define a clopen cylinder in
the marked-group topology.  The literal group makes it nonempty.  The finite
Horn sentence holds in every MF group and forces `w = 1`, so no point of the
cylinder is MF.
