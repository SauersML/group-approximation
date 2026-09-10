---
rg: 2
id: fpbs-conditional-traffic-descent-bound-proof
kind: route
title: Retain edges of expected traffic at least one and charge the rest to repairs
target: fpbs-conditional-traffic-descent-bound
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

Sections 2 to 4 of the artifact. The traffic identity (2.3) is proved by partitioning the request sources according to their chosen finite path word and changing variables at each edge occurrence along an injective partial measure-preserving prefix; a disconnected base request forces either an uncovered source request or a traversed edge whose projected start lies outside the retention set; summing gives the repair bound, and adding the retained domains produces min(1,m_j). This is a supplied deduction, not external validation.
