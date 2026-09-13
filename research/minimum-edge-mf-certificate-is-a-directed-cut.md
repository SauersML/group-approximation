---
rg: 2
id: minimum-edge-mf-certificate-is-a-directed-cut
kind: claim
title: Minimum cost of designated edge relations forcing MF vanishing equals a directed return-path minimum cut
distinct_from:
  directed-seam-mf-closure-is-cycle-pruning: that decides a supplied relation set; this optimizes its cost and gives dual cut and path-packing certificates.
artifacts:
  - research/artifacts/pestov91-optimal-mf-certificates-2026-09-13.md
---

For a nonloop output edge, permitted individual marker involution
relations have minimum sufficient MF cost equal to a permitted directed
cut from the output head to its tail. The weighted problem is polynomial
time. With unit costs and every other edge allowed, the optimum is the
maximum number of edge-disjoint return paths. The output remains
algebraically nontrivial in every allowed input quotient.
