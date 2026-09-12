---
rg: 2
id: one-relator-sofic-via-weinbaum-packet
kind: route
title: Answer Pestov 4.10 by retaining one finite relator packet in an amenable quotient
target: one-relator-groups-sofic
requires:
  - one-relator-weinbaum-packet-amenably-visible
  - proper-subword-amenable-visibility-criterion
artifacts:
  - research/artifacts/one-relator-weinbaum-gate-and-berlai-calibration-2026-08-30.md
---

Write any one-relator presentation as `F/<<v^m>>`, where `v` is not a proper
power.  Free generators not occurring in `v` split off as a free factor.  If
`v` uses only one generator, the group is a free product of a cyclic group and
a free group and is sofic.  Otherwise partition the generators into two
nontrivial free factors so that a cyclic conjugate of `v` has free-product
syllable length at least two.

The first prerequisite supplies an amenable locally indicable quotient that
retains every proper nonempty subword of `v`.  The second prerequisite then
makes the one-relator group sofic.  Free products with the unused free factor
preserve soficity, proving the target.
