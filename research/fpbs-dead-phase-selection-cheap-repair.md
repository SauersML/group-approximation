---
rg: 2
id: fpbs-dead-phase-selection-cheap-repair
kind: route
title: Transfer the finite-sheet saving by selecting one phase and repairing cheaply
target: fpbs-burnside-upper-cost-one
requires: []
artifacts:
  - research/artifacts/fpbs/phase-repair.md
  - research/artifacts/fpbs/responses/22_0909-084654.md
---

Dead: the skew product over a finite cyclic quotient has cost 1+(kappa-1)/q, and the attempt projects one measurable phase down to the base and repairs the broken connections, whose optimal cost is indeed zero. The saving is gone before the repair starts: every single-phase relation has cost exactly kappa, and m selected phases give normalized section cost 1+(kappa-1)/m (fpbs-finite-phase-section-normalization). Section selection followed by cheap repair therefore cannot produce the missing cost-one relation. A fundamentally different transformation of graphings is not ruled out.
