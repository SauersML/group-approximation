---
rg: 2
id: fpbs-optimistic-search-certified-growth-proof
kind: route
title: Preserve known geodesic prefixes and count fresh answers in a finite optimistic ellipse
target: fpbs-optimistic-search-certified-growth
requires: []
artifacts:
  - research/artifacts/fpbs/optimistic-search.md
---

Section 2 proves the known-geodesic tree invariant. Querying back into
the tree would violate the preference for fewer unknown edges among
shortest paths. Conditional expectation at bounded fresh-query stopping
gives the accounting identity. A surviving actual path bounds every
optimistic candidate length; finite ellipse volume bounds distinct
queries and proves connected-case completion. The source note identifies
the existing lazy shortest-path framework and states the limits of its
published finite-graph estimates.
