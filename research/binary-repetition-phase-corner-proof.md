---
rg: 2
id: binary-repetition-phase-corner-proof
kind: route
title: Detect the repeated-letter phase by changes, then flatten the full cyclic corner
target: binary-letter-repetition-realizes-matrix-amplification
requires:
  - binary-pestov-groups-are-three-torsion-generated
artifacts:
  - research/artifacts/pestov91-heteroclinic-prescribed-mf-quotients-2026-09-13.md
---

Section 1 proves the phase images are disjoint: a sequence in two phases
would have changes confined to two different residue classes, forcing
it to be constant. Infinite minimality excludes this. The phases are
clopen, the shift permutes them cyclically, and the return map is the
original system. Full cyclic matrix units identify the crossed product
with the matrix amplification of its zero-phase corner. Elementary
flattening identifies its rank-three group with rank `3k` over the
original ring. Apply the binary Pestov theorem to the repeated system.
