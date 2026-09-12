---
rg: 2
id: aperiodic-hs-bimodule-extension-obstruction-proof
kind: route
title: Use finite spectral support of the restricted semidirect representation
target: aperiodic-module-forbids-prescribed-hs-bimodule-extension
requires:
  - simple-t-augmentation-module-is-aperiodic
---

Restrict the alleged finite-dimensional representation of `M rtimes A` to
`M`.  Conjugation by `A` permutes its character weight spaces while
preserving multiplicity.  Its spectral support is finite, so augmentation
aperiodicity leaves only the trivial character.  The prescribed restriction
therefore acts trivially on `HS_d`.  Evaluating it at `I_d` gives
`rho(s m)=rho(m)`.  Repeating this for the actor generators makes every
character occurring in `rho` actor-fixed, hence trivial.

