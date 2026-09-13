---
rg: 2
id: directed-seam-mf-radical-is-exactly-the-acyclic-edge-kernel
kind: claim
title: A finite directed graph of minimal seams has exactly its noncycle edge kernels as the MF radical
distinct_from:
  aperiodic-seam-mf-radical-is-finitary-already-in-units: that treats one directed transition; this computes the radical for a finite directed graph, retaining every cycle edge in a LEF quotient.
artifacts:
  - research/artifacts/pestov91-directed-seams-and-normal-lattices-2026-09-13.md
---

Construct `X_D` from a finite directed graph by assigning an infinite
minimal binary system to each vertex and a uniquely marked isolated
joining orbit to each edge. Let `B` be the edges between distinct
strongly connected components and `R_D=LC(X_D,F_2) semidirect Z`.

For every `n>=2`, `Rad_MF(EL_n(R_D))` is exactly the product of the
simple finitary kernels on edges in `B`. Its maximal MF quotient is
`EL_n(R_(D\B))`, which is LEF. The same radical formula holds for
`GL_n(R_D)`, `n>=1`, with maximal MF quotient the image of restriction.
Thus these groups are MF exactly when they are LEF, exactly when
every edge of `D` lies on a directed cycle.
