---
rg: 2
id: sparse-fully-branched-covers-iff-sofic-with-connected-links
kind: claim
title: A nonpositively curved 2-complex group with an infinite simple finite-index subgroup and connected vertex links is sofic exactly when it has sparse fully branched covers
distinct_from:
  sparse-fully-branched-covers-iff-sofic-simple-residual: that is the same equivalence with no hypothesis on the links of Y, which is false in that generality unless every such K is nonsofic (it implies titz-witzel-kernel-nonsofic); this adds the hypothesis that makes items 2 and 3 possible at all, and proves the equivalence under it.
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that transfers soficity from sofic fundamental groups of sparse covers and states necessity of sparse branching without the link hypothesis it needs; this needs no soficity of pi_1(X), and reproves necessity under connected links with explicit bookkeeping.
  finite-branched-covers-force-connected-vertex-links: that is the necessary condition and the countermodel; this is the repaired equivalence which uses it for 3 => 1.
  titz-witzel-soficity-is-one-finite-csp: that equates soficity with a marked finite permutation gate; this equates it with a purely geometric existence statement about finite branched covers.
  infinite-simple-group-permutation-stable-iff-nonsofic: that is the algebraic dichotomy for almost homomorphisms of simple groups, imported here; this produces the almost homomorphism from a branched cover and identifies its mark with the mass of the branched components.
---

**ESTABLISHED** (proof: `sparse-fully-branched-covers-iff-sofic-connected-links-proof`).

**Setting.**  `Y` is a finite connected piecewise Euclidean 2-complex with
finitely many shapes, locally CAT(0), not a point; `G = pi_1(Y)`,
`Delta = Y~`.  Finite branched covers `p: X -> Y`, the branch set `B`, the
sheet number `N` and `beta(X)` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` (link coverings of
degree `d_x >= 1`, hence onto, with `Lk(x)` connected).  `X` need not be
connected.  A component of `X` is *unbranched* if it has no branch vertex,
and `X` is *fully branched* if no component is unbranched.  `G` has an
infinite simple subgroup `K` of finite index.

**Theorem.**  The following are equivalent.
1. `K` is sofic (equivalently `G` is sofic), and every vertex link of `Y`
   is connected.
2. For every `eta > 0` there is a fully branched nonempty finite branched
   cover `X` of `Y` with `beta(X) < eta`.
3. There are `c > 0` and nonempty finite branched covers `X_n` of `Y` with
   `beta(X_n) -> 0` whose branched components carry at least a fraction `c`
   of the sheets.

**Corollary.**  If every vertex link of `Y` is connected, then `K` is sofic
if and only if 2 holds, if and only if 3 holds.  This applies to
`Y = Y_1^2`, whose links (the incidence graph of `GQ(2,2)` at `v, w`, and
`K_(3,3)` at `u_1, ..., u_5`) are connected.

**Necessity of sparse branching, repaired.**  Step B0 of the proof shows:
if every vertex link of `Y` is connected and `G` is sofic, then there are
nonempty finite branched covers `X_n` with `beta(X_n) -> 0`.  This is
Part 2 of `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` with the
hypothesis that `finite-branched-covers-force-connected-vertex-links` shows
it cannot do without.

**Contrapositive.**  With connected links, `K` is nonsofic if and only if in
every sequence of nonempty finite branched covers with `beta -> 0` the
fraction of sheets in unbranched components tends to 1.  An unbranched
component is a genuine finite covering of `Y` of degree at most
`[G : G^(infinity)]`.

DERIVATION
sparse-fully-branched-covers-iff-sofic-connected-links-proof
