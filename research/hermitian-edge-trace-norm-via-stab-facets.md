---
rg: 2
id: hermitian-edge-trace-norm-via-stab-facets
kind: route
title: Restricting the trace-norm dual certificate to the support of the threshold vector reduces the Hermitian edge inequality to single facet weights - cliques, odd holes (done) and the rest
target: hermitian-edge-trace-norm-vs-independence
requires:
  - hermitian-edge-trace-norm-clique-inequality
  - hermitian-edge-trace-norm-k4-free-h-perfect
  - hermitian-edge-trace-norm-other-stab-facets
artifacts:
  - research/hermitian-edge-trace-norm-k4-free-h-perfect-proof.md
---

Lane w6-078, 2026-09-18. Full proof: Proposition 6 of
`research/hermitian-edge-trace-norm-k4-free-h-perfect-proof.md`.

**Reduction (both directions).** (**) holds for `G` and all `w >= 0` iff it holds at `(G[S], a)` for
every `S ⊆ V(G)` and every nontrivial facet normal `a` of `STAB(G[S])` with full support `S`.

*Sketch.* By trace-norm duality, (**) for all `w` is equivalent to: `y_+ in STAB(G)` for every
`Q +- C >= 0`, where `y_i = 1 - Q_ii/sqrt3`. Let `T` be the support of `y_+`. Membership reduces to
the facets of `STAB(G[T])`. By Padberg's restriction lemma each such facet, restricted to its support
`S`, is a full-support facet of `STAB(G[S])`. The principal submatrices `(Q_S, C_S)` are again a
feasible pair on `G[S]`, so (**) at that single weight gives the facet inequality for `y`. The converse
direction pads `C` by `1` on the other edges and `w` by `0`.

**Holes.** Full-support facets split into three kinds:
1. cliques, `a = 1`: `hermitian-edge-trace-norm-clique-inequality` (OPEN; true for `m <= 3`);
2. odd holes, `a = 1`: proved, with exact minimum `2 cot(pi/(2n))`, in
   `hermitian-edge-trace-norm-k4-free-h-perfect`;
3. all others (odd antiholes, webs, lifted wheels, ...): `hermitian-edge-trace-norm-other-stab-facets` (OPEN).
