---
rg: 2
id: graph-braid-ascending-matching-complexes-give-sigma-proof
kind: route
title: "Bestvina-Brady Morse theory on the universal cover of UD_n Gamma with ascending links as matching complexes"
target: graph-braid-ascending-matching-complexes-give-sigma
requires: []
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part2.md
---

1. **Cocycle.** In any square of `UD_nΓ`, opposite edges move the same
   particle along the same edge of `Γ`, so they lie in one hyperplane class.
   A hyperplane-constant antisymmetric `c` therefore has zero coboundary on
   every square.
2. **Links.** The cubes at `S` are the sets of moves with distinct sources
   and distinct targets. So `lk(S)` is the matching complex of the move
   graph `B(S)`. A vertex of `X̃` is the minimum of a cube iff every edge of
   the cube at that vertex ascends. So the ascending link is the matching
   complex of `B↑_c(S)`.
3. **Morse lemma.** `h_c` is affine and nonconstant on edges. For `s < t`,
   `X̃_{≥s}` is obtained up to homotopy from `X̃_{≥t}` by coning off
   ascending links of vertices with heights in `[s,t)` (Bestvina–Brady,
   Invent. Math. 129 (1997), §2). With `(m−1)`-connected links the
   inclusion is `m`-connected. `X̃` is contractible and is the increasing
   union of the `X̃_{≥s}`, so every `X̃_{≥t}` is `(m−1)`-connected.
4. **Criterion.** For a free cocompact action on a contractible complex with
   equivariant height, an essentially `(m−1)`-connected superlevel
   filtration gives `[χ] ∈ Σ^m`. See Bux–Gonzalez (J. London Math. Soc. 60
   (1999)) and Witzel–Zaremsky (arXiv:1501.06682, §1).
