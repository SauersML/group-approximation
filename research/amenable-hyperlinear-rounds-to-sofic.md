---
rg: 2
id: amenable-hyperlinear-rounds-to-sofic
kind: claim
title: Amenable hyperlinear microstates round to same-dimension permutation models
artifacts:
  - research/artifacts/rounding-stability-and-free-wreath-audit-2026-08-20.md
distinct_from:
  geometric-schreier-design: that seeks such a permutation shadow for arbitrary finite unitary tables; this theorem assumes the table comes from an amenable group and has regular-trace separation.
  uniform-hs-site-coherence-for-finite-bi-index-pair: that needs one coherent coset lamp family and a same-model capacity trigger; this gives fixed-window permutation rounding only for an amenable group.
---

Let `G` be countable amenable.  For every finite `E subset G` and
`epsilon>0`, there are a finite `F subset G` and `delta>0` such that every
`(F,delta)` hyperlinear approximation `alpha:G -> U(H)` is within squared
normalized-HS error `epsilon` on `E` of a permutation-matrix approximation
induced by an `(E,epsilon)` sofic approximation on the **same** Hilbert space.

The source gives a recursive construction of `F,delta`; for torsion-free
groups its quantitative description is uniform in the group.  The regular
trace-separation hypothesis in “hyperlinear approximation” is essential.

The exact theorem is imported by
`amenable-hyperlinear-to-sofic-same-dimension-citation`.
