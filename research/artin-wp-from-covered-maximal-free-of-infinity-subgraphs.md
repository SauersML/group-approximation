---
rg: 2
id: artin-wp-from-covered-maximal-free-of-infinity-subgraphs
kind: claim
title: An Artin group has solvable word problem when each maximal free-of-infinity subgraph is a product of pieces from the recorded solvable classes
distinct_from:
  known-artin-classes-have-solvable-word-problem: that lists classes of whole Artin groups with an algorithm; this assembles graphs, possibly with infinite labels, whose maximal free-of-infinity subgraphs split into pieces from those classes and two further ones.
  artin-word-problem-reduces-to-free-of-infinity-graphs: that is the general transfer from maximal free-of-infinity subgraphs to the whole group; this applies it to the pieces where an algorithm is recorded in the graph.
---

Let `Γ` be a Coxeter graph on a finite set `S`.

**Hypothesis.** Every maximal free-of-infinity subset `X ⊆ S` admits a partition
`X = X_1 ⊔ ⋯ ⊔ X_k` such that:
- `m_st = 2` whenever `s` and `t` lie in different parts;
- each `Γ_{X_i}` is in one of these classes:
  - right-angled;
  - spherical;
  - irreducible euclidean;
  - FC type;
  - large type;
  - dimension at most 2;
  - rank three;
  - of cyclic type;
  - with no pairwise distinct `x, y, z` satisfying `m_xy = 3`, `m_xz = 2` and
    `m_yz ∈ {2, 3, 4}`.

**Statement.** Then `A_Γ` has solvable word problem.

See route `artin-wp-from-covered-maximal-free-of-infinity-subgraphs-proof`.

**Example not covered by `known-artin-classes-have-solvable-word-problem`.**
- Take two copies of the hyperbolic Coxeter 4-cycle with labels `(3,3,3,4)`.
- Glue them at one vertex.
- Give every remaining pair of vertices from different copies the label `∞`.

The maximal free-of-infinity subsets are the two 4-cycles, which are of cyclic type. The
group has rank 7. It is not of type FC, since a 4-cycle is not spherical. It has
dimension 3, because the triple `A_3` sits in a 4-cycle.

*Referee remark (2026-09-16).* This first example is new only relative to the graph. It
appears to satisfy the hypotheses of the Haettel–Huang gluing theorem (arXiv:2305.11622v2,
Theorem F, source label `thm:intro garside`), which would already make `A_Γ × Z` Garside.
- Every complete subgraph of the presentation graph lies in one 4-cycle, so it is a
  cyclic-type graph or a spherical one.
- The only cyclic-type induced subgraphs are the two 4-cycles, and `Λ^⊥` is empty for
  each of them.
- Every 4-cycle of the presentation graph lies in one copy, where all pairs are joined,
  so it has a diagonal.
- Orienting each Dynkin 4-cycle cyclically gives the required orientation.

**Example that needs the assembly.**
- Take the `(3,3,3,4)` 4-cycle on `a, b, c, d`, with `m_ab = m_bc = m_cd = 3`,
  `m_da = 4` and `m_ac = m_bd = 2`.
- Take the path `[5,3,5]` on `a, f, g, h`, with `m_af = 5`, `m_fg = 3`, `m_gh = 5` and
  label 2 on the other pairs.
- Give every pair with one vertex in `{b, c, d}` and one in `{f, g, h}` the label `∞`.

The maximal free-of-infinity subsets are `{a, b, c, d}` (cyclic type) and `{a, f, g, h}`.
The second has no triple `m_xy = 3`, `m_xz = 2`, `m_yz ∈ {2, 3, 4}`: the only label 3 is
`m_fg`, and the vertices commuting with `f` or with `g` are `h` and `a`, where
`m_gh = m_af = 5`. So the hypothesis holds. None of the single imported results applies
to the whole group:
- not the recorded classes (4-cycle not spherical, `A_3` triple `b, c, d`, rank 7, not
  a join);
- not Theorem 1.1 of arXiv:2412.12195 (the `A_3` triple `b, c, d`);
- not Haettel–Huang Theorem F (the complete subgraph `{a, f, g, h}` is `[5,3,5]`, which is
  neither spherical nor cyclic type nor a join);
- not Godelle–Paris Theorem C as stated, which assumes every free-of-infinity Artin group.
