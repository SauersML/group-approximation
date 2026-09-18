---
rg: 2
id: branched-cover-monodromy-reduction-without-connected-links
kind: claim
title: The monodromy construction of sparse branched covers works on locally CAT(0) 2-complexes whose vertex links are allowed to be disconnected
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
