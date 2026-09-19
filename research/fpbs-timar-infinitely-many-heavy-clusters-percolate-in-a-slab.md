---
rg: 2
id: fpbs-timar-infinitely-many-heavy-clusters-percolate-in-a-slab
kind: claim
title: If Bernoulli percolation on a nonunimodular transitive graph has infinitely many heavy clusters, then the open subgraph of some slab has an infinite cluster
distinct_from:
  fpbs-hyperbolic-and-nonunimodular-nonuniqueness: that imports Hutchcroft's p_c < p_h <= p_u; this imports Timar's structural theorem about the phase with infinitely many heavy clusters, which that node does not state.
---

**ESTABLISHED (imported, secondary).** Proof route:
`fpbs-timar-heavy-clusters-slab-cite`.

**Definitions** (Hutchcroft, arXiv:1711.02590v3, Section 1.1).

- `G` is a connected, locally finite graph and `Gamma <= Aut(G)` is
  transitive and nonunimodular. `Delta(x,y) = |Stab_y x| / |Stab_x y|` is the
  modular function. It is `Gamma`-invariant and satisfies the cocycle
  identity `Delta(x,z) = Delta(x,y) Delta(y,z)`.
- A set `K` of vertices is **heavy** if `sum_(y in K) Delta(x,y) = infinity`
  for some (equivalently every) vertex `x`, and **light** otherwise.
- A **slab** is a set `{u in V : e^s <= Delta(v,u) <= e^t}` with `v in V` and
  `s < t`.
- `p_h(G,Gamma) = inf{p : G[p] contains a heavy cluster almost surely}`.

**Theorem (Timar 2006, Theorem 5.5, as quoted by Hutchcroft).** Let `G` be a
connected, locally finite graph and `Gamma` a transitive nonunimodular
subgroup of `Aut(G)`. If Bernoulli bond percolation `G[p]` has infinitely many
heavy clusters almost surely, then there is a slab `S` such that the open
subgraph of `S` contains an infinite cluster almost surely.

**Companion facts from the same source.**

- For percolation clusters, being heavy is almost surely equivalent to having
  infinite intersection with some slab (Timar 2006, Lemma 5.2, as quoted by
  Hutchcroft). The direction "infinite slab intersection implies heavy" is
  elementary: by the cocycle identity `Delta(x,y) >= Delta(x,v) e^s` on the
  slab, so the sum diverges.
- `p_t <= p_h <= p_u`, where `p_t` is the tiltability threshold.

Status records an imported theorem, read from Hutchcroft's paraphrase. The
primary source, A. Timar, "Percolation on nonunimodular transitive graphs",
Ann. Probab. 34 (2006), was not read.
