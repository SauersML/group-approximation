---
rg: 2
id: mf-extension-nonclosure
kind: claim
title: MF groups are not closed under extensions
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralWitnessConsequences.lean
---

There is a short exact sequence whose kernel and quotient are MF but whose
middle group is not MF.  Concretely,
`1 -> ClLamp(X) -> W -> V -> 1` has locally finite MF kernel, residually finite
MF quotient, and non-MF total group.
