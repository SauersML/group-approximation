---
rg: 2
id: mf-extension-nonclosure-proof
kind: route
title: Use the lamp-by-linear structure of the sofic non-MF witness
target: mf-extension-nonclosure
requires: [sofic-non-mf-witness]
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/LiteralWitnessConsequences.lean
  - GroupApproximation/Sofic/LocallyFiniteMF.lean
---

## Why sufficient

The Clifford lamp kernel is locally finite and hence MF.  The quotient `V`
is a finitely generated subgroup of `GL_4(Q)`, so Malcev's theorem makes it
residually finite and therefore MF.  The middle group is the established
non-MF witness `W`.
