---
rg: 2
id: sparse-fully-branched-covers-iff-sofic-simple-residual
kind: claim
title: A nonpositively curved 2-complex group with an infinite simple finite-index subgroup is sofic exactly when it has sparse branched covers in which every component is branched
invalidates:
  - nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers
distinct_from:
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that transfers soficity from sofic fundamental groups of sparse covers and records that its two parts do not combine to an equivalence; this needs no soficity of pi_1(X) at all (it uses the trivial pi_1(X)-model) and, when a finite-index subgroup is infinite simple, gives an honest equivalence by replacing freeness with a connectivity mark.
  titz-witzel-soficity-is-one-finite-csp: that equates soficity with a marked finite permutation gate; this equates it with a purely geometric existence statement about finite branched covers, whose mark is supplied by connectivity through a descent argument.
  kazhdan-consistent-partial-models-round-to-finite-actions: that rounds consistent partial models of a Kazhdan group to genuine finite actions; this uses no property (T), and the genuine actions that appear are the unbranched components of a cover, detected geometrically by descending a developing map.
  infinite-simple-group-permutation-stable-iff-nonsofic: that is the algebraic dichotomy for almost homomorphisms of simple groups, imported here; this produces the almost homomorphism from a branched cover and identifies its mark with the mass of the branched components.
  titz-witzel-kernel-nonsofic-iff-consistent-deletion-repair: that states nonsoficity of the kernel as deletion repair of almost solutions of its relators; this states it as the collapse of every sparse branched cover onto unions of genuine covers, with no relator bookkeeping and no Kazhdan constant.
---

**OPEN.**  An attempted proof is `sparse-fully-branched-covers-iff-sofic-proof`;
refereeing found a missing hypothesis in the import used by its Step B (see
`## Attempts`).  Step A (3 => 1) is not in doubt.

**Setting.**  `Y`, `G = pi_1(Y)`, `Delta = Y~`, finite branched covers
`p: X -> Y`, the branch set `B` and the branching mass `beta(X)` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`.  `X` need not
be connected.  A connected component `C` of `X` is *unbranched* if it
contains no branch vertex.  Then `p|_C` is a genuine finite covering of `Y`.
`X` is *fully branched* if it has no unbranched component.  Assume `G` has
an infinite simple subgroup `K` of finite index.

**Theorem.**  The following are equivalent.
1. `K` is sofic (equivalently, `G` is sofic).
2. For every `eta > 0` there is a fully branched finite branched cover `X`
   of `Y` with `beta(X) < eta`.
3. There are `c > 0` and finite branched covers `X_n` of `Y` with
   `beta(X_n) -> 0`, whose branched components carry at least a fraction
   `c` of the sheets.

No hypothesis is made on `pi_1(X)`: the conclusion holds even if all these
groups are nonsofic.

**Contrapositive form.**  `K` is nonsofic if and only if, in every sequence
of finite branched covers with `beta -> 0`, the fraction of sheets lying in
unbranched components tends to 1.  Every connected unbranched component has
degree at most `[G : G^(infinity)]`, the index of the finite residual.  So
nonsofic sparse covers are asymptotically disjoint unions of boundedly many
kinds of genuine covers.

## Consequences for the Titz Mite--Witzel complex

These are consequences *if* the theorem is established; they are not
currently available.  The links of `Y_1^2` are connected, so the repair
proposed in `## Attempts` would not cost this section anything.

Take `Y = Y_1^2` and `K` its simple finite residual
(`titz-witzel-simple-kazhdan-cat0-lattices-exist`).

* **Flat hitting alone gives soficity.**  An unbranched component is a
  genuine cover of `Y`, with universal cover the building `Delta`.  Every
  apartment is a Euclidean plane, and its `R`-disks immerse locally
  isometrically into the component, which lies in `X \ B`.  So condition
  (H) of `flat-hitting-branched-covers-have-hyperbolic-pi1` forces `X` to
  be fully branched.  Hence `titz-witzel-flat-hitting-sparse-branched-covers`
  alone implies `titz-witzel-kernel-sofic`, through the route
  `titz-witzel-kernel-sofic-via-flat-hitting-covers`.  Neither the girth
  condition (G) nor `titz-witzel-flat-hitting-branched-cover-groups-are-sofic`
  is needed: in `titz-witzel-kernel-sofic-via-branched-hyperbolization`
  that prerequisite is redundant.
* **The hyperbolic contrapositive is vacuous.**  The route
  `nonsofic-hyperbolic-group-from-titz-witzel-flat-hitting-covers` needs
  `titz-witzel-kernel-nonsofic` and `titz-witzel-flat-hitting-sparse-branched-covers`
  together.  By the first bullet these are inconsistent, so that route can
  never produce a nonsofic hyperbolic group.  It would be invalidated (the
  `invalidates` entry above takes effect only once this claim is
  established; while this claim is OPEN the route stands).  The
  remark there that "whichever way soficity goes this converts into
  hyperbolic groups" is false.  If the kernel is nonsofic, the flat-hitting
  covers do not exist.
* **What remains.**  Soficity of the kernel would become equivalent to one
  combinatorial statement: sparse branched covers of `Y_1^2` whose branched
  part carries a fixed fraction of the sheets.  Nonsoficity would be
  a rigidity statement: every sparse branched cover is, up to `o(N)` sheets,
  copies of `Y_1^2` and its genuine double cover.

## Attempts

- 2026-09-17 (swarm-0917, d-tfs-p2): proposed as ESTABLISHED via
  `sparse-fully-branched-covers-iff-sofic-proof`; set back to OPEN after
  refereeing.  Two of three referees found no gap; the third refuted the
  statement as written.  The proof files are kept as the attempt.
  * **The gap (Step B, 1 => 2).**  Step B imports Step 4 of
    `sparse-branched-covers-sofic-pi1-reduction-proof`.  That step silently
    needs every vertex link of `Y` to be connected: it takes a free basis of
    `pi_1(S_y)` for the link sphere `S_y`, it needs `Y°` connected so that
    `pi_1(Y°) -> G` is onto (used verbatim at the top of Step B here), and it
    needs each added cone point to have a connected link covering `Lk(y)`.
    Neither the Setting above nor the imported
    `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` states this.
    That claim's Setting asks only that in a *cover* each `Lk(x)` be connected
    and cover `Lk(p x)`; it says nothing about the links of `Y` itself.
  * **Counterexample to the stated generality.**  Let `Y' = Y_1^2` with a flat
    unit square glued at one corner to a vertex.  `Y'` is finite, connected,
    piecewise Euclidean with finitely many shapes and locally CAT(0) (the new
    link pieces are arcs, with no cycles), and it has the same `G` and the
    same infinite simple `K`.  But the link of the glued vertex is the old
    link together with a disjoint arc.  Under the convention above, a branched
    cover needs each `Lk(x)` connected and covering `Lk(p x)`, so `Y'` admits
    no finite branched cover at all: items 2 and 3 are false for `Y'` while
    item 1 is open.  The theorem as stated would therefore prove
    `titz-witzel-kernel-nonsofic`, which is open, with no argument.  For `Y'`,
    Step 4 breaks concretely: `Y'°` is disconnected and `S_y` is not connected.
  * Under the opposite convention, where link coverings need not be onto,
    branched covers of `Y'` do exist, but then the Setting's assertion that an
    unbranched component is a genuine covering fails (used in Step D), as does
    Lemma 1's claim that the star of a degree-1 vertex maps isomorphically.
  * **What survives.**  Step A (3 => 1) was checked independently by all three
    referees and stands: the almost homomorphism `Sigma_n(g)(t) = kappa(g*t~)`,
    the invariance (INV) of Lemma 5 via Lemmas 2.1--2.3, the descent to a
    `K`-invariant local homeomorphism with open, compact, connected image, the
    pigeonhole mark, and the use of
    `infinite-simple-group-permutation-stable-iff-nonsofic` ((1) => (2),
    contrapositively).  Within Step B, the argument that unbranched orbits
    factor through `G` and are fixed by `u` also stands.
  * **Proposed repair.**  Add to the Setting the hypothesis that every vertex
    link of `Y` is connected, and propagate it to
    `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`.  The links of
    `Y_1^2` are connected, so the Titz--Witzel corollary would survive the
    repair; that has not been re-refereed and the fixed statement is not
    recorded as a separate claim.
  * Bookkeeping noted in passing, not a gap: the chaining bound in Step B
    should use `Sigma(u^(-1))`-style terms rather than `Sigma(k)^(-1)`, which
    turns `(l+1) epsilon` into `O(l epsilon)`.
