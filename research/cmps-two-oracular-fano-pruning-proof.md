---
rg: 2
id: cmps-two-oracular-fano-pruning-proof
kind: route
title: Combine radius-two commutation with line-hitting empty links
target: culf-mastel-rstar-halt-model-has-fano-cap-support
requires:
  - cmps-two-oracular-rstar-lift-has-commuting-context-stars
  - cmps-rstar-lift-has-line-hitting-empty-links
  - fano-pruning-is-line-hitting-empty-link
---

Choose the perfect completeness model from the CMPS-to-`R_*` lift.  Its
incident context algebras commute mutually, so their assignment PVMs admit
the joint refinements used in the empty-link pruning argument.  By the
line-hitting hypothesis, each Fano line contains an atom with no compatible
joint neighborhood assignment.  The corresponding projection is zero.
Therefore every local positive support misses at least one point of every
Fano line and is a Fano cap, which is exactly the target claim.

No assertion is made that 2-oracularizability supplies the line-hitting
hypothesis: that implication is refuted by
`distance-two-oracularity-does-not-force-fano-pruning`.
