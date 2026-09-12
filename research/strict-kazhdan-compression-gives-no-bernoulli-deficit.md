---
rg: 2
id: strict-kazhdan-compression-gives-no-bernoulli-deficit
kind: claim
title: A strict compression of an infinite Kazhdan subgroup does not by itself force a Bernoulli Rokhlin entropy deficit
distinct_from:
  median-matching-has-no-bernoulli-entropy-analogue: that shows the median device has no Kazhdan components to match on the shift; this shows the compression relation itself is realized in a residually finite group whose Bernoulli shifts are Rokhlin-maximal.
  a-t-menable-groups-have-no-rigid-compression-defect: that shows a-T-menable groups contain no rigid pair with a defect; this exhibits a rigid pair with a strict compressor inside a sofic group, and reads it against entropy deficits.
  linear-scale-rank-conservation-does-not-kill-defects: that calibrates the rank-metric conservation theorem on the literal group E; this calibrates Bernoulli entropy deficits on the Kun--Thom actor.
artifacts:
  - research/artifacts/measurable-alphabet-compression-2026-09-12.md
---

Let `Gamma = EL_r(F_q[x_1..x_d]) < G` be the Kun--Thom Theorem E pair of
`kun-thom-actor-is-rf-but-neither-rfd-nor-llp`: both are infinite, finitely generated, residually
finite and Kazhdan, and `G` contains a strict compressor `t`, with `t Gamma t^-1` a proper subgroup of
`Gamma` (used in `surjunctive-groups-carry-invisible-rigid-defects`, part 2). Then every uniform
Bernoulli shift over `G` has Rokhlin entropy `log q`. So `G` has no measurable alphabet compression
and no finite deficit configuration.

**Reading for the measurable negative target.**
- A deficit configuration over `U = L_(F_2)(1,2)^x` whose incidence pattern is realized injectively
  in `G` is impossible, since the functional `Phi` depends only on the pattern.
- The compressor code idea (one output symbol mixing input symbols along `t Gamma t^-1 < Gamma`)
  therefore cannot get its saving from the strict compression, the Kazhdan property, or their
  combination. It must use a relation of `U` that fails in the Kun--Thom actor.
- The natural such relation is a rigid defect `[t z t^-1, gamma]` with `z` centralizing `Gamma`. The
  surjunctive Kun--Thom LEF-lamp wreaths already carry nontrivial ones, and whether they are
  Rokhlin-maximal is open. Section 7 of the artifact.

**ESTABLISHED 2026-09-12** by [[strict-kazhdan-compression-no-deficit-proof]].
