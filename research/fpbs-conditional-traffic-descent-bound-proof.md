---
rg: 2
id: fpbs-conditional-traffic-descent-bound-proof
kind: route
title: Retain edges of expected traffic at least one and charge the rest to repairs
target: fpbs-conditional-traffic-descent-bound
requires:
  - fpbs-infinite-contact-zero-relative-cost
artifacts:
  - research/artifacts/fpbs/docs/shared-component-repair.md
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
  - research/artifacts/fpbs/responses/51_0909-211602.md
---

Sections 2 to 4 of the artifact. The traffic identity (2.3) is proved by partitioning the request sources according to their chosen finite path word and changing variables at each edge occurrence along an injective partial measure-preserving prefix; a disconnected base request forces either an uncovered source request or a traversed edge whose projected start lies outside the retention set; summing gives the repair bound, and adding the retained domains produces min(1,m_j). This is a supplied deduction, not external validation.

Section 9 extends this to arbitrary countable groups with finite-cost base.
Fix a finite-cost generating base graphing Lambda. Its prefix gives finitely
many partial-domain requests to which the same traffic calculation applies.
Append all unprocessed maps directly in both source and base, charging their
full tail cost in r. Every Lambda-request is then connected, so the completed
graphings generate. The tail adds no conditional traffic defect because it
is base measurable. This is a direct repair construction; it does not use
subgroup exhaustion or assume that an infinite-cost base has a cheap tail.

For the component-repair alternative, apply the required zero-relative-
cost theorem to S=R_F whenever its infinite-contact hypothesis holds.
Append its arbitrarily cheap repair to F to obtain C(X)<=c(F).
This use does not assume that every threshold graphing has the
necessary contacts or that a random graph law can be realized on X.
