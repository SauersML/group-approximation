---
rg: 2
id: cmsz-pg23-rs-two-graphs-admit-no-brick-coding
kind: claim
title: Two explicit Robertson–Steger tile 2-graphs of CMSZ groups over PG(2,3) admit no brick coding in any dimension
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
  - experiments/nv-brick-coding-2026-09-17/tp_q3.json
  - experiments/nv-brick-coding-2026-09-17/check_q3.py
  - experiments/nv-brick-coding-2026-09-17/q3_hypotheses.py
  - experiments/nv-brick-coding-2026-09-17/q3_hypotheses.log
distinct_from:
  cmsz-pg22-rs-two-graphs-admit-no-brick-coding: that treats five q = 2 presentations, where a SAT certificate is needed; this treats two q = 3 presentations, where the Kraft/Perron step alone kills every brick coding.
---

Let `PG(2,3)` have points `Z/13` and lines `{i, i+1, i+3, i+9}`. The file
`experiments/nv-brick-coding-2026-09-17/tp_q3.json` records two point–line bijections:

- T0: `λ = [6,7,8,1,5,4,10,11,12,2,3,9,0]`
- T1: `λ = [11,1,2,0,12,8,10,4,6,9,5,7,3]`

Each has a triangle presentation `T` satisfying (A1)–(A3), checked by `check_q3.py`.
`Λ_T` is the tile 2-graph built by `rs2graph.build(T, npoints=13)`, with the same rules as
in `cmsz-pg22-rs-two-graphs-admit-no-brick-coding`. It has 156 tiles, `1404 + 1404`
edges and 12636 squares.

**Claim.** For both `T`, `Λ_T` has no brick coding (B1)–(B3) in any dimension.

Route: `cmsz-pg23-no-brick-coding-by-kraft`.
