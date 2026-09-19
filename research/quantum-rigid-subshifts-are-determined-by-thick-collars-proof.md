---
rg: 2
id: quantum-rigid-subshifts-are-determined-by-thick-collars-proof
kind: route
title: "Glue two extensions of a collar pattern across a thick cut and apply the two-piece certificate; read off entropy, countability, finite fibres and Toeplitz wire nets"
target: quantum-rigid-subshifts-are-determined-by-thick-collars
requires:
  - rigid-subshift-amenability-from-coherent-variation-caps
  - quantum-rigid-subshifts-cluster-the-modifications-of-each-point
  - quantum-rigidity-passes-to-subshifts
  - rigid-subshifts-over-free-factors-are-tight-almost-everywhere
  - time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows
---

Lane proof by bh-ra-proof, 2026-09-19. Not independently reviewed. The argument is the `## Proof` section
of `quantum-rigid-subshifts-are-determined-by-thick-collars`. It uses these inputs:
- the two-piece certificate (Lemma 1′ of `rigid-subshifts-over-free-factors-are-tight-almost-everywhere`)
  for item 1;
- coarse connectivity and unboundedness of modification supports (item 1 of
  `rigid-subshift-amenability-from-coherent-variation-caps`) for items 2 and 6;
- monotonicity (`quantum-rigidity-passes-to-subshifts`) for items 3 and 4;
- the Reiter maps of the caps node for item 5(b);
- the fibre bookkeeping of `time-lifts-reduce-ra-prime-to-automorphism-groups-of-rigid-rows` for the
  calibration of item 5(c).

The standard facts it uses are recalled, not re-read:
- the variational principle for amenable groups (Ornstein–Weiss; Kerr–Li);
- the structure of equicontinuous minimal systems (Ellis);
- Švarc–Milnor;
- countability of scattered compact metrizable spaces.
