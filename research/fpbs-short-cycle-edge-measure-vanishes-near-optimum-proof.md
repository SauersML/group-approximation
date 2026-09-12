---
rg: 2
id: fpbs-short-cycle-edge-measure-vanishes-near-optimum-proof
kind: route
title: Delete each edge that tops its chosen shortest cycle under a random finite ranking
target: fpbs-short-cycle-edge-measure-vanishes-near-optimum
requires: []
artifacts:
  - research/artifacts/fpbs/docs/cost-cycle-structure.md
---

Section 2 of the artifact, Theorem 2.1. Choose one shortest cycle per edge measurably before priorities are assigned. Deleting an edge whose chosen cycle has all other edges of strictly smaller finite priority preserves the generated relation, by induction on the finitely many priority values. Refining finite partitions separate the finitely many cycle edges outside a set of arbitrarily small edge measure; independent uniform atom priorities, replaced by their ranks, delete each nonexceptional edge with probability exactly the reciprocal of its shortest-cycle length, and some deterministic ranking attains the expected deletion mass. This is a supplied deduction, not external validation.
