---
rg: 2
id: branched-cover-monodromy-reduction-without-connected-links
kind: claim
title: The monodromy construction of sparse branched covers works on locally CAT(0) 2-complexes whose vertex links are allowed to be disconnected
refuted_by:
  - finite-branched-covers-force-connected-vertex-links
distinct_from:
  sparse-branched-covers-with-sofic-pi1-give-sofic-lattice: that is the soficity transfer itself, whose Setting quantifies over branched covers and says nothing about the links of the base; this isolates the base-side hypothesis that its proof's Step 4 silently uses when it builds a cover from a sofic model.
  sparse-fully-branched-covers-iff-sofic-simple-residual: that is the equivalence between soficity and fully branched sparse covers; this is the one missing input to its Step B, and is stated purely about the construction, with no simple subgroup and no soficity anywhere in it.
  titz-witzel-soficity-is-one-finite-csp: that is a finite permutation gate equivalent to soficity of one particular kernel; this is a general position statement about a geometric construction, and is expected to be false as stated rather than open-and-plausible.
---

**OPEN**, and expected to be false as stated; see the counterexample below.
It is recorded because it is the exact hypothesis that
`sparse-fully-branched-covers-iff-sofic-simple-residual` needs and does not
have, and because naming it keeps that claim honestly OPEN instead of
silently established through a route with an unstated premise.

**Setting.**  `Y` is a finite connected piecewise Euclidean 2-complex with
finitely many shapes which is locally CAT(0), and `G = pi_1(Y)`.  Branched
covers `p: X -> Y`, the branch set and `beta(X)` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`, so each
`Lk(x) -> Lk(p x)` is a covering of finite graphs with `Lk(x)` connected.

**Claim.**  Step 4 of `sparse-branched-covers-sofic-pi1-reduction-proof`, the
construction that turns an `(F, epsilon)`-sofic model of `G` into a finite
branched cover of `Y` with `beta = O(epsilon)`, applies to every such `Y`,
with no further hypothesis on the vertex links of `Y`.

**Why it is wanted.**  Step B (1 => 2) of
`sparse-fully-branched-covers-iff-sofic-proof` imports that step verbatim,
including the sentence "the `k_i` generate `G`, since `pi_1(Y°) -> G` is
onto".  Without it, only Step A (3 => 1) of that proof survives, and
`sparse-fully-branched-covers-iff-sofic-simple-residual` is OPEN.

**What the imported step actually uses.**  Three things, each needing every
vertex link of `Y` to be connected.
* A free basis of `pi_1(S_y)` for the link sphere `S_y`.
* `Y°`, the complement of the cone points, connected, so that
  `pi_1(Y°) -> G` is onto.
* Each added cone point to have a connected link covering `Lk(y)`.

**Counterexample to the claim as stated.**  Let `Y'` be `Y_1^2` with a flat
unit square glued at one of its corners to a vertex.  `Y'` is finite,
connected, piecewise Euclidean with finitely many shapes and locally CAT(0)
(the new link pieces are arcs, so no angular girth is lost), and
`pi_1(Y') = pi_1(Y_1^2)`.  The link of the glued vertex is the old link
together with a disjoint arc.  Under the covering convention above no finite
branched cover of `Y'` exists at all, so no construction can produce one, and
Step 4 breaks concretely: `Y'°` is disconnected and `S_y` is not connected.
Under the opposite convention, where the link covering need not be onto,
branched covers of `Y'` do exist, but then the separate assertion that an
unbranched component is a genuine covering of the base fails, as does the
claim that the star of a degree-1 vertex maps isomorphically.

**The expected resolution is to refute this and restrict instead.**  Add "every
vertex link of `Y` is connected" to the Setting of
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` and of
`sparse-fully-branched-covers-iff-sofic-simple-residual`.  The links of
`Y_1^2` are connected, so the Titz--Witzel consequences would be unaffected.
Nobody has written the restricted statements down or refereed them, so that
repair is not yet available either.

## Attempts

- 2026-09-17 (swarm-0917, d-tfs-p2): created while landing the referee verdict
  on `sparse-fully-branched-covers-iff-sofic-simple-residual`.  No attempt has
  been made to prove it; the counterexample above is the reason to expect a
  refutation rather than a proof, and the useful next move is the restriction,
  not this claim.
- 2026-09-18 (swarm-0917-w7-w7-titz-last1, minimal-counterexample): **refuted
  and restricted.**
  * *Refutation.*  `finite-branched-covers-force-connected-vertex-links`
    (proof `finite-branched-covers-force-connected-vertex-links-proof`, no
    prerequisites): onto link coverings make `p(X)` open, closed and all of
    `Y`, so a base with a nonempty finite branched cover has connected vertex
    links.  The minimal countermodel is the wedge `W` of two unit squares at a
    corner: contractible, locally CAT(0), `pi_1 = 1` sofic, and no finite
    branched cover at all.  Step 4 applied to `W` would produce one.  The same
    shows Part 2 of `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`
    is false as stated (Parts 1 and 3 unaffected).
  * *Restriction.*  `sparse-fully-branched-covers-iff-sofic-with-connected-links`
    (proof `sparse-fully-branched-covers-iff-sofic-connected-links-proof`)
    proves the equivalence with "every vertex link of `Y` is connected" added
    to item 1.  Step B0 redoes Step 4 under connected links: `Y°` connected,
    `Y°` retracts to a finite graph, van Kampen with path-connected
    intersections, cone points with connected links, and the word bound
    `(W)` (`2 l epsilon n`, fixing the `Sigma(k)^(-1)` bookkeeping).
  * *Consequences.*  `titz-witzel-kernel-sofic-via-connected-link-covers`
    routes `titz-witzel-kernel-sofic` with the single open prerequisite
    `titz-witzel-flat-hitting-sparse-branched-covers`.
    `titz-witzel-kernel-nonsofic-from-unrestricted-cover-equivalence` records
    that the unrestricted `sparse-fully-branched-covers-iff-sofic-simple-residual`
    implies `titz-witzel-kernel-nonsofic`.
