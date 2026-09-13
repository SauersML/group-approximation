---
rg: 2
id: directed-seam-mf-closure-is-cycle-pruning
kind: claim
title: The entire MF closure operator on a directed-seam group deletes exactly the remaining noncycle edges
distinct_from:
  directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel: that computes the ambient radical; this computes the radical after every normal quotient using the incidence labels.
  hereditarily-mf-quotients-have-principal-camouflage-closure: that closure adjoins one fixed normal subgroup; this closure changes with the return paths destroyed by the input quotient.
artifacts:
  - research/artifacts/pestov91-mf-closure-and-monotone-rules-2026-09-13.md
---

For the directed-seam group and its normal subgroup `N(J,S)`, let
`B_J` be the edges of `D\J` not lying on a directed cycle. Then
`cl_MF(N(J,S))=N(J union B_J,S)`. Every normal quotient is MF exactly
when it is LEF, and the closed normal subgroups are precisely the
pairs whose retained graph has every edge on a cycle.

For a retained edge `e:a->b`, its simple factor is in this closure
exactly when no directed return path from `b` to `a` remains. If a
path remains, a LEF target killing `N(J,S)` embeds that factor.
