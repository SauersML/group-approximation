---
rg: 2
id: rips-segev-two-layer-elements-have-no-left-annihilator
kind: claim
title: In Steenbock's Rips--Segev group, alpha (u + w b^{±1}) != 0 for every nonzero alpha and every u, w in k[a^{±1}] with w != 0, over every field; a nowhere-zero flow on a leaf block of the port graph replaces the harmonic cycle, and a walk that hops between copies every 3 to 5 cosets is a relation of K that Greendlinger's lemma forbids
distinct_from:
  rips-segev-two-layer-cycles-split-over-copies: that reduces only the half u(1) + w(1) = 0 to a linked-cycle lemma proved for at most 14 copies; this proves a stronger linked-cycle lemma for every number of copies and removes the condition u(1) + w(1) = 0.
  rips-segev-three-copy-configurations-carry-no-zero-divisors: that excludes configurations covered by at most three copies (and N copies only when 3N^2 - N < 5 gamma/8 - 1); this excludes every left annihilator of a two-layer element, with no bound on the number of copies.
  rips-segev-core-large-gap-two-layer-elements-are-regular: that needs a large gap in the a-support; this has no condition on u and w beyond w != 0.
  rips-segev-groups-satisfy-kaplansky-zero-divisor: that is the open question; this settles the left-annihilator side of its two-layer case (b-degree one).  The right-annihilator side (u + w b) alpha = 0 and b-degree at least two stay open.
---

**ESTABLISHED (proposed; unreviewed).**  Derivation: `rips-segev-two-layer-no-left-annihilator-proof`.

**Setting.**  As in `rips-segev-two-layer-cycles-split-over-copies`.
- `G` is the Rips--Segev group built from Steenbock's graph `Gamma`, and `K = F/<<R>>` is its core,
  `F = <a> * <b>`, with `Gr'_*(1/8)` and `girth(Phi) >= 42`.
- `Cay` is the Cayley graph of `K` on `{a, b}`.  A *copy* is `C = h g(Gamma) ⊆ Cay`.  The lines of `Gamma` are
  the vertices of `Phi`, and its `b`-edges are the edges of `Phi`.
- `k` is any field.  `u, w in k[t^{±1}]` are evaluated at `a`.

**Theorem 1 (hopping lemma).**  Let `c = c_1 + ... + c_N` (`N >= 1`) be a sum of nonzero cycles
`c_i in Z_1(C_i; k)` in pairwise distinct copies.  Then some `C_i` has at least three *untouched* cycle lines:
lines of `C_i` meeting a `b`-edge of `supp c_i`, in whose coset no `c_j`, `j != i`, is nonzero on any edge.
- This is the linked-cycle lemma of `rips-segev-two-layer-cycles-split-over-copies` for every `N`, with three
  untouched lines in place of two.  It is coefficient-free and uses no row structure.
- The proof walks through the cycle supports, staying 3 to 5 cosets in each copy, until the walk closes up.  The
  closed walk is a cyclically reduced relation of `K`.  By Greendlinger's lemma it has 13 consecutive `b`-edges
  in one copy.  But any 13 consecutive `b`-edges contain 4 consecutive cosets of each of two distinct copies,
  and two distinct copies share at most 3 cosets.

**Theorem 2 (no left annihilators).**  Let `alpha in k[G]` and `u, w in k[t^{±1}]`, with `w != 0`.
If `alpha (u + w b) = 0` or `alpha (u + w b^{-1}) = 0`, then `alpha = 0`.
- Equivalently, applying `g -> g^{-1}`: `(u' + b^{±1} w') beta = 0` with `w' != 0` forces `beta = 0`.
- The condition `u(1) + w(1) = 0` of the earlier reduction is not needed.
- *Mechanism.*
  - Let `S` be the graph on left `<a>`-cosets with an edge `y <a> -- y b <a>` whenever `(alpha w)(y) != 0`.
    Every active coset has degree at least 2 in `S`.
  - A leaf 2-edge-connected block `B` of `S` carries a nowhere-zero `k(s)`-flow.  Filling it along the cosets
    gives a nonzero cycle on `Cay`.
  - At a vertex of `B` other than its bridge end, every port edge lies in `B`.  So an untouched cycle line there
    is pure, and the rank-one lemma allows at most one of them per copy.
  - That makes at most two untouched cycle lines per copy, which contradicts Theorem 1.

**Scope.**
- Settled: the left-annihilator side of the two-layer case of `rips-segev-groups-satisfy-kaplansky-zero-divisor`.
  No zero-divisor pair `alpha x = 0` has `x = u + w b^{±1}`.  This covers the whole sequence of `N`-copy attempts
  (one, two, three copies, the linked-cycle reduction), for the left side.
- Calibration: the model `<a, b | (a^m b)^n>` has `sum_j (a^m b)^j (1 - a^m b) = 0`.
  - Its flow cycle is the single relator loop, so `N = 1` and all `n` lines are untouched.  Theorem 1 holds there.
  - What fails is the bound of one pure line per copy: all `n` lines carry the same port pattern, so the
    rank-one lemma has nothing to separate.  Distinct rows of the lines of `Gamma` are the essential input.
- **Open.**
  - The right-annihilator side: `(u + w b) alpha = 0`, equivalently `beta (w' + b u') = 0` with `b` to the left of
    the coefficient.  The port equation `X(zb) = -Y(z)` becomes `X(b z) = -Y(z)`, which links left cosets
    `z <a>` to `b z <a>` rather than to `z b <a>`.  The coset graph `S` and the walk in Theorem 1 have no
    counterpart for it yet.
  - `b`-degree at least two.
