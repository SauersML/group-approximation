---
rg: 2
id: wave5-audit-two-heisenberg-sector-rank-proof
kind: route
title: Explicit shift and clock representations and exact F8 face ranks
target: wave5-audit-two-heisenberg-sectors-have-zero-h1
requires:
  - wave4-visibility-k7-marked-face-presentation
artifacts:
  - research/artifacts/hyperbolic-rf-wave5-audit-2026-09-20.md
---

The exact script
`experiments/hrf-wave5-heisenberg-2026-09-20/sectors.py`
constructs the two representations from the seven-dimensional
class-two Lie structure. It checks all basis-pair BCH identities,
finite vertex relations, and all six marked face identities.

Vertex averaging turns cocycles into three principal parameters.
The stacked face constraint matrices have ranks 96 and 12 in
module dimensions 49 and 7. Each module has vertex fixed-space
dimensions (1,1,0) and global fixed-space dimension zero. Therefore
`dim H^1=2d-r-sum dim V^Hj+dim V^K=0` in both cases.

Arithmetic uses the exact field F2[t]/(t^3+t+1). The root agent
independently read and replayed the computation and returned PASS.
