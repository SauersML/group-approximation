---
rg: 2
id: zero-dimensional-system-mf-radical-is-core-restriction
kind: claim
title: Exact locally finite MF radicals and LEF core quotients hold for all compact metrizable zero-dimensional systems over F2
root: true
distinct_from:
  subshift-mf-radical-is-the-locally-finite-core-kernel: that assumes a finite-alphabet subshift; this removes the symbolic and expansive hypotheses entirely.
  short-period-free-low-rank-mf-radical-is-core-kernel: that proves full low-rank kernels for subshifts; this covers every zero-dimensional compact metrizable system under the same short-period hypotheses.
artifacts:
  - research/artifacts/pestov91-zero-dimensional-universal-core-reflection-2026-09-13.md
  - non_mf_groups_exist.tex
---

For coefficient field `F_2` and rank at least four, the MF radical
of the elementary or general linear crossed-product group is exactly
the locally finite kernel of restriction to the chain-recurrent core.
The elementary quotient is the core elementary group; the general
linear quotient is its restriction image. Both are LEF.

If no period below `k` occurs, the formula holds whenever `nk>=4`,
for `GL_n` with `n>=1` and `EL_n` with `n>=2`. Thus rank two and units
are covered for every aperiodic compact metrizable zero-dimensional
system. No finite generation or property (T) of these general ambient
groups is asserted.

The manuscript section `sec:chain-core` now prints the full kernel
proof as `thm:core-mf-radical`, with the improved general linear
threshold three from `three-coordinate-linear-groups-detect-chain-recurrence`.
Its return-section corollary also prints rank two without fixed points
and units without periods one or two. Those stronger GL bounds are
recorded separately in `three-return-levels-give-exact-mf-unit-reflection`.
The manuscript claims have paper-proof status, not Lean status.
