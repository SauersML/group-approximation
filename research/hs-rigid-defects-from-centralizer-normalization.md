---
rg: 2
id: hs-rigid-defects-from-centralizer-normalization
kind: route
title: Hilbert--Schmidt centralizer normalization kills every rigid defect in hyperlinear groups
target: hyperlinear-groups-kill-rigid-compression-defects
requires: [kt-centralizer-normalization-hs, rigid-compression-defect-normalization-dichotomy]
artifacts:
  - research/artifacts/rigid-compression-defect-ladder-2026-09-11.md
---

1. Take an injective representation of the hyperlinear group `H` into a
   tracial matrix ultraproduct with canonical trace.
2. Its restriction to the pair is trace-preserving, so the normalization
   hypothesis applies.
3. Normalization carries every centralizing `z` into the relative commutant
   after conjugation by `g`, so the rigid defect dies.

This is the `NORM => DD` half of the dichotomy in the hyperlinear class.

**Cycle, on purpose.** Together with
`hs-centralizer-normalization-from-rigid-defects`, this route records an
equivalence, so `cairn check` reports a dependency cycle. The least fixpoint
never fires on it, and both implications are true. Do not delete either route
to silence the warning.
