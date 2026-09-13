---
rg: 2
id: graph-braid-matching-complex-connectivity-explicit
kind: claim
title: "The (m-1)-connectivity of matching complexes of ascending move graphs of UD_n Gamma has a closed graph-theoretic description"
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
---

For the bipartite move graphs `B↑(S)` that arise at configurations of `UD_nΓ`,
`(m−1)`-connectivity of the matching complex is decided by an explicit
condition on degrees and connectivity of `B↑(S)`.

## Attempts

- 2026-09-13 (z1-08-graph-braid): the case `m = 1` should be elementary.
  The matching complex of a bipartite graph is connected iff the complement
  of its line graph is connected. That fails only in star-like and
  triangle-free small cases, so the list of exceptions is expected to be
  short. For higher `m`, chessboard complexes are the full bipartite case,
  with connectivity bounds by Björner–Lovász–Vrećica–Živaljević. General
  bipartite subgraphs need a new bound, e.g. a Nerve/Quillen fiber argument
  on the source particles.
