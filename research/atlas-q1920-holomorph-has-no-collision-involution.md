---
rg: 2
id: atlas-q1920-holomorph-has-no-collision-involution
kind: claim
title: The natural holomorph of either marked Q1920 has no nontrivial collision involution centralizing the first radial S3
artifacts:
  - experiments/atlas_a4_q1920_automorphism_seam.g
  - research/artifacts/atlas-a4-q1920-holomorph-seam.json
distinct_from:
  atlas-q1920-seam-has-no-low-index-action: that excludes transitive permutation actions through degree twelve; this exhausts every affine automorphism of Q1920, independent of its permutation degree.
  atlas-q1920-is-radial-holonomy-extension: that classifies the local module and radial mismatch; this uses that structure to fence the most natural finite overgroup construction.
---

Fix either marked `Q=Q1920` and its first radial `A=<r,u>`.  In the natural
holomorph `Hol(Q)=Q semidirect Aut(Q)`, enumerate every affine element which
centralizes `A` pointwise.  There are exactly 7,680 such elements, including
463 involutions.

For an involution `c`, impose the two remaining marked collision equations

```text
(c t)^3 = 1,
t c s c t^-1 c s t c = 1.                                (Q1920-HOL-1)
```

In each marking exactly one pointwise-centralizing element satisfies
`(Q1920-HOL-1)`, and it is `c=1`.  Hence no nontrivial collision involution,
and therefore no faithful collision `S4` or seam `S3=<c,z>`, can be realized
inside the natural holomorph of either marked local vertex.

This does not prove that the universal F/J colimit collapses.  A general
completion need not normalize `Q`, so its collision involution need not lie
in `Hol(Q)`.
