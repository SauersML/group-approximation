---
rg: 2
id: coherent-records-have-exact-phase-energy-proof
kind: route
title: Proof of coherently recording basis information has an exact hypercube phase-energy formula
target: coherent-records-have-exact-phase-energy
requires: []
artifacts:
  - research/artifacts/qpcp-full-target-continuation-2026-09-20.md
  - research/artifacts/check-qpcp-full-target-continuation-2026-09-20.py
  - research/artifacts/qpcp-full-target-continuation-replay-2026-09-20.json
---

Evaluate <X_i> by pairing overlaps across hypercube edges.
Reverse edges make the sum real; the identity
||phi_x-phi_y||^2=2-2Re<phi_x,phi_y> gives the formula.
Classical orthogonal records contribute squared distance two exactly
when they differ. Count all edges for parity, 2n edges for AND,
and none for a constant. For one bit directly trace out the record;
the pure-state trace distance is sqrt(1-|<u,v>|^2), obtained from
the two eigenvalues of the projector difference. Sections 3.1–3.2
give the complete proof and sharpness.

