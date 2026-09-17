---
rg: 2
id: cmsz-pg22-no-brick-coding-by-corners
kind: route
title: Check (R1)–(R3) exactly for the five PG(2,2) tile 2-graphs and apply the corner kill, with no SAT solver
target: cmsz-pg22-rs-two-graphs-admit-no-brick-coding
requires:
  - rank-two-h1-tile-two-graphs-admit-no-brick-coding
artifacts:
  - research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md
  - experiments/nv-brick-coding-2026-09-17/tp_q2.json
  - experiments/nv-brick-coding-2026-09-17/rs2graph.py
  - experiments/nv-brick-coding-2026-09-17/certificate.py
  - experiments/nv-brick-coding-2026-09-17/certificate.log
  - experiments/nv-brick-coding-2026-09-17/certificate_uniform.log
---

Details: Part G of `research/artifacts/nv-brick-coding-corner-kill-2026-09-17.md`.

1. **Model and hypotheses.** `rs2graph.build` asserts (H1) for T0..T4. `certificate.py nosat`
   checks (A1)–(A3). For T0 the log records verbatim: "row sums 4; primitive exponents
   5,5; dim H^1 = 2; one transport class per colour". The same line appears for T1..T4 in
   `certificate_uniform.log`, with "primitive exponents 4,4" for T2.
   - Primitive implies irreducible, which gives (R1).
   - (R2) comes from a lower bound on the `GF(p)` rank of the coboundary plus the
     independence of `[d_1]` and `[d_2]`, as in Part C of
     `research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md`.
   - (R3) comes from union–find.
2. **Conclusion.** `rank-two-h1-tile-two-graphs-admit-no-brick-coding`
   gives no brick coding in any dimension for each T.

**Trust base.** Exact modular rank bounds and union–find. This route uses part (b) of
`two-graph-brick-codings-are-rigid-under-rank-two-h1` but not its dimension bound (c),
and it uses no SAT solver. It is independent of the solver runs in
`cmsz-pg22-no-brick-coding-certificate`.
