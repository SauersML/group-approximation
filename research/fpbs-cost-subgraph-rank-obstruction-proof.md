---
rg: 2
id: fpbs-cost-subgraph-rank-obstruction-proof
kind: route
title: Intersect two commuting extensions of a free-group treeing
target: fpbs-cost-subgraph-rank-obstruction
requires:
  - fpbs-cost-one-backbone-fixes-completion-bill
artifacts:
  - research/artifacts/fpbs/docs/cost-rank-duality.md
---

Take the a_i,z edges for A and the a_i,w edges for B in a free
F_r x Z^2 action. Their intersection is the free-group treeing,
whose cost is r by Gaboriau's treeing theorem. Each of A,B and
their union generates a cost-one action: retain a full commuting
central direction and restrict other generators to an arbitrarily
small complete section for that direction. Their common cost is
one by the aperiodic lower bound. These imported facts and the
explicit section-routing argument are documented in Section 1.

The four costs violate both proposed rank properties. Applying
total-cost normalization to each restricted graphing identifies
every restriction-consistent candidate with this failed setfunction.
Finally use the required claim's relative-cost upper bound with
ambient cost one to obtain zero relative completion cost. Inclusion
of the intersection edges nevertheless forces edge cost at least r.

The literature comparison in Section 3 is an audit of a different
rank and of the additional planar connectivity input, not a claim
that the cited authors imposed restriction consistency on their
open cost-matroid question.
