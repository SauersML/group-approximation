---
rg: 2
id: artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring-proof
kind: route
title: Prove that the four dead-edge sums of the graph K generate the unit ideal in every ring
target: artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring
requires: []
artifacts:
  - research/artifacts/zp-artin-sigma1-dead-edge-rings-2026-09-13.md
---

Direct proof, in the target's body and artifact §6 (F2).

- Admissible partitions: `u1u2` and `v1v2` have label 2 and are never dead, so each pair
  lies on one side, and both sides need a live vertex.
- Ring computation: `ū1 v̄1 = -1 = ū2 v̄1` forces `ū1 = ū2`; then `ū1 v̄2 = -1` and the
  label-6 sum equals `1`.

The commuting relations of `A_K` are not even needed.
