---
rg: 2
id: finite-adaptive-tree-via-morita-trace
kind: route
title: Use the finite Morita trace law instead of a full coefficient decoder
target: non-hyperlinear-group
requires:
  - mipstar-bcs-tracial-nonru-exists
  - maximal-forbidden-atom-has-a-named-positive-half
  - finite-adaptive-selected-atom-ring-tree
  - atlas-steinberg-context-absorption
  - marked-hs-separation-forces-spectral-density
  - murray-von-neumann-arrow-has-a-steinberg-conjugacy-witness
  - orthogonal-idempotent-sum-has-a-stabilized-steinberg-conjugacy
  - hs-steinberg-morita-trace-additivity-on-adaptive-blocks
---

Start from the canonical Pauli seed of ambient density `1/4`.  At the
maximal type of every reached node, `(MTA3)` and `(MFA1)` give source mass at
least `beta/M` times the current carrier mass.  Equations `(MTA1)--(MTA2)`
add that mass to the child.  Choose the fixed depth so that the resulting
geometric growth exceeds one.  The finite sum of microstate errors vanishes,
contradicting total normalized mass one.  The perfect tracial BCS model sends
all conditional sources and arrows to zero and keeps the central mark.
