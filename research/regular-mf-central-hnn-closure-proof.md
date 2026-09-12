---
rg: 2
id: regular-mf-central-hnn-closure-proof
kind: route
title: Combine Shulman's central-HNN MF theorem with the reduced-HNN regular trace
target: regular-mf-central-hnn-closure
requires: []
artifacts:
  - notes/REGULAR_MF_BASS_SERRE.md
---

Apply Shulman's central-HNN theorem to the MF algebra in a regular realization.
Map the resulting universal algebra to the reduced von Neumann HNN extension
of the GNS closures.  Conditional expectation onto the edge algebra kills
every group element outside the edge subgroup, so the reduced-word moment
formula assigns trace zero to every nonidentity Britton-reduced word.  This
detects the group normal form and pulls the regular character back to the MF
algebra.  The complete calculation is in the attached artifact.
