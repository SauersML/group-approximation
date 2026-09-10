---
rg: 2
id: fpbs-unit-target-search-ellipse-proof
kind: route
title: Prove optimal first-discovery depths and bound priorities along an open witness path
target: fpbs-unit-target-search-ellipse-bound
requires: []
artifacts:
  - research/artifacts/fpbs/search-geometry.md
---

Section 2 gives a first-counterexample argument using the consistent
ambient distance heuristic. Before termination each side has an unprocessed
witness-path edge of priority at most L. Both endpoints of every queried
edge then lie in the ellipse, and the cache counts each edge once.
Counting tree vertices by distance from the endpoint geodesic and summing
over allowed heights gives the exact product volume.
