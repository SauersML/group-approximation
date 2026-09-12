---
rg: 2
id: fg-simple-hyperlinear-tree-group-proof
kind: route
title: Import Le Boudec's groups, run amenable-edge permanence on the Bass-Serre graph, and read non-finite-presentation off the lamplighter
target: fg-simple-hyperlinear-tree-group-not-finitely-presented
requires:
  - amenable-edge-graph-corners-cannot-groupify-a-nonce-game
---

**Clauses 1, 2 (citation).**  Le Boudec, *Simple groups and irreducible
lattices in wreath products*, arXiv:2001.08689v1, read from the PDF on
2026-09-11.
- Section 2.1: `G(F,F')` is countable iff `F` is semi-regular.  When it is,
  `G(F,F')` is finitely generated [LB16, Cor. 3.8], and "stabilizers of
  vertices are infinite locally finite subgroups" [LB16, Section 3.1].
- The abstract and the Applications paragraph: Theorem 1.2 combined with the
  simplicity results of [LB16, Section 4.2] gives finitely generated simple
  groups with the Cayley graph of a wreath product.

**Clause 4 (citation plus standard facts).**
- Le Boudec's Theorem 1.2: `G(F,F')` acts properly and cocompactly on the
  lamplighter graph of `C_n wr W_d`, so it is quasi-isometric to that
  wreath product, and so is its index-two subgroup.
- Finite presentability is a quasi-isometry invariant of finitely generated
  groups.
- G. Baumslag (Math. Z. 75, 1961): a restricted wreath product `A wr B` with
  `A != 1` is finitely presented only when `B` is finite.  `W_d` is infinite
  for `d >= 3`.

**Clause 3 (derivation).**  `H = G(F,F')^*` preserves the bipartition, so it
acts on the tree without inversions.  By Bass--Serre theory, `H` is the
fundamental group of its quotient graph of groups: the vertex groups are
vertex stabilizers and the edge groups are edge stabilizers.  All of these are
subgroups of locally finite groups, hence locally finite and amenable, and in
particular hyperlinear.  A finite generating set of `H` lies in the
fundamental group of some finite connected subgraph of groups, which injects
into `H` and therefore equals `H`.  That finite graph of groups has amenable
edge groups and hyperlinear vertex groups, so `H` is hyperlinear by
`amenable-edge-graph-corners-cannot-groupify-a-nonce-game`.  `G(F,F')`
contains `H` with index two and is hyperlinear by the same argument applied
to its barycentric subdivision.  Soficity follows as well from the sofic
amalgam permanence theorems, but that is not wired here.
