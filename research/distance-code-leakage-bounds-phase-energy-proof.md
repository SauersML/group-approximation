---
rg: 2
id: distance-code-leakage-bounds-phase-energy-proof
kind: route
title: Proof of leakage delta from a label-diagonal code changes normalized energy by at most square root delta
target: distance-code-leakage-bounds-phase-energy
requires:
  - distance-code-local-tests-are-label-diagonal
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

Normalize P rho P and purify rho. Projection of the purification
has overlap sqrt(Tr(P rho)) with the original, so their trace distance
is at most sqrt(delta). Contract under partial trace and test with
the effect K to bound the energy change. Dephase the normalized
projection in the logical label: the prerequisite's diagonal
compression preserves its energy. Section 3.4 contains the full
purification and effect argument.

