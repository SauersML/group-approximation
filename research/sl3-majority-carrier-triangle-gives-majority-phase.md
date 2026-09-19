---
rg: 2
id: sl3-majority-carrier-triangle-gives-majority-phase
kind: route
title: Apply the native parahoric triangle on the synchronized majority carrier
target: sl3-joint-hecke-multiplicity-has-a-majority-phase-sector
requires:
  - sl3-joint-parahoric-loops-share-a-majority-carrier
  - native-parahoric-triangle-kills-all-corrector-gauges
artifacts:
  - research/artifacts/sl3-one-parahoric-multiplicity-flow-audit-2026-08-21.md
---

On the majority carrier supplied by the first prerequisite, the relative
transport gauge is fixed by the relevant parahoric root words and satisfies
the rank-two triangle relation with vanishing defect.  Apply the
dimension-free estimate `(NPC15)` from the second prerequisite.  After the
projective scalar normalization already supplied by perfectness, the
relative gauge converges to the identity on that carrier.  Its conjugate
fold word therefore converges to one common phase there.

The carrier trace is at least `1/2+kappa`, so it supplies `(JHM1)` and hence
the majority-phase terminal.  The spectator no-go explains why neither
prerequisite may be replaced by a one-edge expansion estimate.
