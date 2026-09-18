---
rg: 2
id: cmsz-pg22-rs-two-graphs-admit-no-brick-coding
kind: claim
title: Five explicit Robertson–Steger tile 2-graphs of CMSZ groups over PG(2,2) admit no brick coding in any dimension
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
  - experiments/nv-brick-coding-2026-09-17/tp_q2.json
  - experiments/nv-brick-coding-2026-09-17/rs2graph.py
  - experiments/nv-brick-coding-2026-09-17/certificate_uniform.py
  - experiments/nv-brick-coding-2026-09-17/certificate_uniform.log
distinct_from:
  robertson-steger-a2-two-graphs-are-primitive-and-aperiodic: that concerns primitivity and aperiodicity of RS 2-graphs in general; this proves, for five explicit q = 2 examples, that no brick coding exists.
  two-graph-brick-codings-are-rigid-under-rank-two-h1: that is the general rigidity proposition; this applies it to explicit presentations, with a SAT certificate.
---

Let `PG(2,2)` have points `Z/7` and lines `{i, i+1, i+3}`. The file
`experiments/nv-brick-coding-2026-09-17/tp_q2.json` records five point–line bijections:

- T0: `λ = [0,1,2,4,6,5,3]`
- T1: `λ = [0,1,2,5,4,6,3]`
- T2: `λ = [0,1,2,6,4,5,3]`
- T3: `λ = [0,1,3,2,4,6,5]`
- T4: `λ = [0,1,3,5,4,2,6]`

Each comes with a triangle presentation `T` satisfying (A1)–(A3), found by exact cover.

**Setup.** `Λ_T` is the finite 2-graph built by `rs2graph.py`.

- **Vertices.** There are 42 tiles `(x,y,z,u,w)` with `(x,y,z), (y,u,w) ∈ T` and
  `u ≠ z`.
- **Edges.** A colour-1 edge `a -> b` exists iff `w_a = z_b` and `y_a ≠ x_b`. A colour-2
  edge `a -> c` exists iff `u_a = x_c` and `w_a ≠ y_c`.
- **Squares.** The 672 squares are the shape-(2,2) words, and unique filling is asserted
  by the script.

**Claim.** For each `T ∈ {T0,…,T4}`, `Λ_T` has no brick coding (B1)–(B3) in any
dimension `m ≥ 1`. So Theorem A of `brick-coded-two-graph-full-groups-embed-in-brin-thompson`
gives no embedding `[[Λ_T]] ↪ mV` for any `m`.

The identification of `Λ_T` with the Robertson–Steger 2-graph `Λ_{Γ_T}` is not part of
this claim.

Route: `cmsz-pg22-no-brick-coding-certificate`.
