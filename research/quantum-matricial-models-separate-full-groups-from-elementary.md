---
rg: 2
id: quantum-matricial-models-separate-full-groups-from-elementary
kind: claim
title: Some minimal topologically free Cantor action has a matricial crossed product without a combinatorial model, and its topological full group and Kazhdan elementary groups have different approximation types
distinct_from:
  labbe-tiles-admit-periodic-quantum-tilings-at-every-scale: that asks whether Labbé's tiles admit periodic quantum tilings at every scale; this asks whether quantum (non-combinatorial) matricial models can separate LEF of the full group from LEF of the elementary groups, for any action.
  lrf-cantor-actions-give-lef-full-and-elementary-groups: that proves the two agree whenever a combinatorial model exists; this asks what happens when only quantum models exist.
artifacts:
  - research/artifacts/un-full-groups-bridge-2026-09-13-part1.md
---

**OPEN.** There is a minimal, topologically free action `α` of a finitely generated group on the Cantor set such that
`R = LC(X,F_q) ⋊ Γ` embeds in some `∏_ω M_N(F_q)` but has no combinatorial matricial model, and exactly one of the
following holds:
- `[[α]]` is LEF, or
- `EL_n(R)` (`n >= 3`) is LEF.

**Why this is the right frontier.** By `lrf-cantor-actions-give-lef-full-and-elementary-groups`, a combinatorial model
exists iff `α` is locally residually finite, and then both groups are LEF. So any divergence between the full-group
side (Grigorchuk–Medynets, Ma, Matui, Nekrashevych) and the Kazhdan side (Pestov 9.1) must live among actions with only
quantum models.

## Attempts

- **Labbé's Ω_U (test case).** `Z^2` acts freely and minimally, and an invariant measure exists.
  - Artifact Prop 3.1: for `Z^d`, LRF means genuine finite `Z^d`-actions following `α` on large balls.
  - That is Kerr–Nowak residual finiteness without density. It fails for SFTs without finite orbits, by the periodic
    configuration argument in `sfts-without-finite-orbits-are-not-residually-finite-actions`. That argument uses one
    point `z_0`, a genuine action, and closeness on the SFT shape only; density is not used.
  - So there is no combinatorial model. A matricial model exists iff the tiles admit noncommuting periodic quantum
    tilings at every scale (`matricial-z2-sft-crossed-products-give-quantum-tilings`).
  - On the full-group side, LEF of `D([[Ω_U]])` is open (`labbe-shift-derived-full-group-is-lef`). Every recorded
    mechanism there (Kakutani–Rokhlin towers, periodic approximations, Ma's Theorem C) is combinatorial and dies.
  - Where it stops: both sides are open. A quantum tiling would make `EL_n` LEF while every combinatorial route to LEF
    of `[[Ω_U]]` is dead. That is exactly the separation, if `[[Ω_U]]` is not LEF.
- **Restriction of a quantum model to permutation units.**
  - A matricial model sends each full bisection unit to an invertible matrix, i.e. into `∏_ω GL_N(F_q)`, which is an
    ultraproduct of finite groups.
  - So LEF of `EL_n(R)` through a model always gives LEF of `[[α]]`. The separation can only go the other way: `[[α]]`
    LEF with `R` not matricial.
  - This rules out one direction for rings with a matricial model. It does not rule out `EL_n(R)` being LEF without any
    matricial model of `R` (open converse `lef-el-groups-force-exactly-matricial-simple-ring`).
- **Candidate for `[[α]]` LEF with `R` not matricial.**
  - Actions without an invariant measure have no matricial model (`matricial-steinberg-algebras-have-invariant-measures`).
  - Their full groups can still be LEF only through towers that do not intertwine the clopen algebra, which Ma's
    residual-finiteness framework forbids.
  - No example known.

**Review (un-verify-open, 2026-09-13, `research/artifacts/un-review-open-2026-09-13-part2.md`): Display checked (OPEN node); the restriction argument in Attempts is correct.**
