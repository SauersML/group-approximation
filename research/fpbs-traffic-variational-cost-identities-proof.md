---
rg: 2
id: fpbs-traffic-variational-cost-identities-proof
kind: route
title: Truncate near-optimal graphings and lift target plans to get both identities
target: fpbs-traffic-variational-cost-identities
requires: []
artifacts:
  - research/artifacts/fpbs/docs/fixed-price-conditional-traffic.md
---

Section 5 of the artifact. For the source identity, split a near-optimal countable graphing into restrictions of group transformations, truncate to finitely many maps and one path-length bound, and use that the generating set is finite and every request has a finite path almost surely, so the uncovered measure is arbitrarily small. For the target identity, the descent bound is one direction; conversely lift a finite approximation of a near-optimal target plan, whose decisions and hence traffic are base measurable and integer valued, so its defect is exactly zero. This is a supplied deduction, not external validation.
