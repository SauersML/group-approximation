---
rg: 2
id: graph-product-normal-forms-and-rf-permanence
kind: claim
title: Graph products have reduced-word normal forms and preserve residual finiteness over finite graphs
artifacts:
  - research/artifacts/lef-graph-wreath-surjunctivity-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Let `Lambda` be a simplicial graph with vertex set `X`, let `(A_x)` be groups,
and let `Lambda(A)` be their graph product: the free product of the `A_x`
modulo `[A_x, A_y]` for every edge `{x,y}`.

1. **Normal form.** A word of syllables `(a_1)_(x_1) ... (a_l)_(x_l)` is
   *reduced* when every coefficient is nontrivial and no two syllables at the
   same vertex can be brought together by interchanging neighbouring syllables
   at adjacent vertices. Every element has a reduced representative, and a
   nonempty reduced word represents a nontrivial element.
2. **Residual finiteness.** If `Lambda` is finite and every `A_x` is residually
   finite, then `Lambda(A)` is residually finite.

Both are due to Green (*Graph products of groups*, thesis, Leeds, 1990). The
LEF graph wreath artifact also records a modern proof of (2) for monoids,
Cho--Gould--Ruskuc--Yang, arXiv:2403.13614, Theorem 5.1.

`lef-graph-wreath-via-finite-lamp-tables` consumes (2) for the finite
induced subgraph products `N_S`, and (1) for the syllable reductions in its
local-embedding lemma.
