---
rg: 2
id: full-mf-radical-marked-openness-proof
kind: route
title: Word conditions are clopen and the inequality passes to every group satisfying them
target: full-mf-radical-locus-is-open-in-marked-groups
requires:
  - full-mf-radical-linear-relator-inequality
artifacts:
  - research/artifacts/mf-radical-linear-certificate-2026-09-07.md
---

## Proof

Identify a marked group with its set of relations, a subset of `F_m`, and
give `G_m` the induced product topology.  For a fixed word `r` the set
`{H : r=1 in H}` is a cylinder on one coordinate, so it is clopen, and a
finite intersection of such sets is clopen.

Let `(G,(g_i))` have `Res_MF(G)=G` and take `r_1,...,r_s` and `C` from
`(LIN)`.  The set `N` where every `r_j` is a relation is clopen and contains
`(G,(g_i))`.  If `H in N` then each `r_j` is a relation of `H`, and `(LIN)`
mentions `H` only through those words, so it holds for `H` with the same
constant; the converse half of
`full-mf-radical-linear-relator-inequality` gives `Res_MF(H)=H`.

Choosing `v` nontrivial in `G` and intersecting with the clopen set
`{H : v != 1 in H}` leaves a clopen neighbourhood of `(G,(g_i))` all of whose
members are nontrivial.
