---
rg: 2
id: return-reachability-gives-optimal-mf-cut-certificates
kind: route
title: Reachability extracts a no-more-expensive cut from every sufficient relation set and integral flow gives the dual packing
target: minimum-edge-mf-certificate-is-a-directed-cut
requires:
  - directed-seam-mf-closure-is-cycle-pruning
  - monotone-mf-implications-use-commuting-involution-relators
artifacts:
  - research/artifacts/pestov91-optimal-mf-certificates-2026-09-13.md
  - research/artifacts/minimize-pestov91-edge-mf-relations-2026-09-13.py
  - research/artifacts/check-pestov91-optimal-mf-certificates-2026-09-13.py
  - research/artifacts/pestov91-optimal-finite-receipt-2026-09-13.json
---

Section 3 translates MF implication into loss of all return paths.
Residual reachability extracts the optimum cut; the integral flow
argument proves unit-cost path-packing duality. Forbidden edges get
capacity greater than the sum of all allowed costs.
