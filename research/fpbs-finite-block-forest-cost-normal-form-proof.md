---
rg: 2
id: fpbs-finite-block-forest-cost-normal-form-proof
kind: route
title: Attach the prescribed block trees to a near-optimal complete-section graphing
target: fpbs-finite-block-forest-cost-normal-form
requires:
  - fpbs-small-marker-induction-input
artifacts:
  - research/artifacts/fpbs/docs/relative-cycle-exchange.md
---

Section 5. Orient the prescribed forest toward its transversal to get
c(F)=1-q. Any graphing of R|A joins representatives, and adjoining F
then generates R at cost 1-q+q c(J). The imported induction identity
identifies its infimum with C(R). Freeness makes a factor map bijective
on orbits, so the lifted finite blocks have the same sizes and their
transversal has the same measure. Apply induction on both sides and
subtract the two finite cost identities to get D=q D_A.
