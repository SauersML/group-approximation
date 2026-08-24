---
rg: 2
id: simple-kl-via-l2-betti-normal-rank
kind: route
title: Force normal rank greater than one using positive first l2-Betti number
target: kl-holds-over-two-generator-simple-groups
requires: []
artifacts:
  - research/artifacts/kl-cyclic-orbit-audit-2026-08-24.md
---

Try to replace the failed abelianization certificate by a positive first
`l2`-Betti number and an inequality of the shape

    beta_1^(2)(G) <= normal-rank(G)-1.

Such an inequality would obstruct one-element normal generation whenever the
left side is positive.  It is unavailable in the reduced problem: the simple
coefficient factors may have torsion, and
`torsion-breaks-l2-normal-rank-bound` records simple torsion groups of normal
rank one with arbitrarily large first `l2`-Betti number.  Positivity therefore
cannot supply the proposed normal-rank conclusion without exactly the
torsion-free hypothesis missing here.
