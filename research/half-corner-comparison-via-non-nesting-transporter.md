---
rg: 2
id: half-corner-comparison-via-non-nesting-transporter
kind: route
title: Install the chart comparison through one Thompson transporter that relabels whole chart blocks
target: half-corner-chart-comparison-exists
requires: []
artifacts:
  - research/artifacts/kaplansky-transporter-exterior-screen-2026-09-12.md
---

**Dead.** Invalidated by `non-nesting-transporters-cannot-install-chart-comparison`.

The approach: take `Z = P_0 [h] f_0` for one prefix permutation `h` whose pulled-back
leaves `h^-1 (000, 001, 010, 011)` are cones never properly nested with the chart
leaves. This includes all uniform-depth transporters and the depth-changing
relabelings of whole blocks. The hope was a left inverse `L` with `L Z = f_0`.

The two charts then generate a finite block group. There the comparison would
be an isomorphism of induced projectives, and the block module separates them
by rank, 0 against 2.

Recorded with `requires: []` only so the invalidation has a target; it asserts
nothing while its invalidator is established.
