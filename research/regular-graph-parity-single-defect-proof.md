---
rg: 2
id: regular-graph-parity-single-defect-proof
kind: route
title: Paths transport the unique odd charge to each target vertex of a regular circulant
target: regular-graph-parity-has-uniform-single-defects
requires: []
artifacts:
  - research/artifacts/qpcp-strengthened-amplification-2026-09-20.md
  - research/artifacts/check-qpcp-strengthened-amplification-2026-09-20.py
  - research/artifacts/qpcp-strengthened-amplification-replay-2026-09-20.json
---

For even `r` take the circulant with steps `±1,...,±r/2`. For odd `r`
take steps `±1,...,±(r-1)/2` plus the antipodal perfect matching. With
`m` even and `m>r`, the edges are distinct, the degree is `r`, and the
step-one cycle connects the graph.

The binary incidence matrix `A` has two ones in every column, so its image
has even total parity. The target charge `b=e_0` is odd: every assignment
violates at least one constraint. For each target vertex `v`, the indicator
of a path from zero to `v` has incidence `e_0+e_v`, including the empty
path for `v=0`. Its violation syndrome `Ax+b` is exactly `e_v`.
Thus the minimum number of violations is one and a uniformly sampled
target gives exactly `1/m` violation probability at every vertex.
Diagonality makes quantum energies convex combinations of classical ones,
so the same minimum holds over all quantum states.

Section 4 of the artifact gives the full FCC application. The exact
script checks all target syndromes in 27 graphs of arities 2 through 10,
with independent exhaustive minimization on small cases.
