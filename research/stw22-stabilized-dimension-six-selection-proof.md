---
rg: 2
id: stw22-stabilized-dimension-six-selection-proof
kind: route
title: Apply degree-five half-slack selection over six-dimensional bases
target: stw22-dim6-factor-bundles-have-uniform-traces
requires:
  - stw22-half-slack-all-factor-weighted-s5-fillings
  - stw22-dim5-factor-bundles-have-uniform-traces
  - stw22-tracefree-fibre-gap-ideals-force-trace-continuity
artifacts:
  - research/artifacts/stw22-dim6-factor-bundle-breakthrough-2026-08-31.md
---

For fixed `m>=3` and a global half-slack weight, stabilization and the
factor-uniform correction lemma give a lower-semicontinuous family of
nonempty closed weighted-copy values in one complete Hilbert space.  The
degree-zero through degree-five theorems make it five-connected and
equi-`LC^5`.  Michael with `n=5` applies over bases of dimension at most
six; operator-ball recovery returns the selected tuple to the algebra.

For each arbitrary `m>=3`, the usual spectral/central cut makes a positive
gap representative have support below `1/(2m)`.  The selected `m` copies
give `m sigma([c])<=||sigma||`.  Let `m` tend to infinity and remove the
spectral cut; the exact gap criterion proves the claim.

