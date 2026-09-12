---
rg: 2
id: thom-hyperlinear-kazhdan-without-factorization
kind: claim
title: Thom constructed a hyperlinear Kazhdan group without Kirchberg's factorization property
artifacts:
  - research/artifacts/thom-0810-2180-verified.md
distinct_from:
  thom-central-corner-criterion: that imports the central-character criterion from Lemma 3.3 of the same paper; this imports the paper's counterexample from its abstract and construction.
---

There exists a sofic (hence hyperlinear) group `G` with property (T) which
does not have Kirchberg's factorization property.  Equivalently, the canonical
trace on `C^*(G)` is not amenable despite `G` admitting faithful tracial
matrix-ultraproduct models.

This is Andreas Thom, *Examples of hyperlinear groups without factorization
property*, Groups Geom. Dyn. 4 (2010), arXiv:0810.2180.  The checked primary
source record is `research/artifacts/thom-0810-2180-verified.md`.

**Stability consequence.**  This example is not residually finite: a
residually finite group has exact regular finite-quotient packets, which
make its canonical trace amenable and give the factorization property.
Hence `non-rf-kazhdan-weak-ucp-iff-non-hyperlinear` says Thom's hyperlinear
Kazhdan group is not weakly ucp-stable; the corrected
`kazhdan-weak-ucp-stability-is-flexible-stability` then says it is not fully
flexibly HS-stable either.  This supplies a concrete negative example for
the corrected equivalence, not a non-hyperlinear group.
