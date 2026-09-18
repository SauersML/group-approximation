---
rg: 2
id: finite-branched-covers-force-connected-vertex-links
kind: claim
title: A 2-complex with a finite branched cover has connected vertex links, so a wedge of two squares is a contractible locally CAT(0) complex with no finite branched cover
distinct_from:
  branched-cover-monodromy-reduction-without-connected-links: that asserts the monodromy construction works with disconnected links; this is the countermodel refuting it, and the general necessary condition behind it.
  branched-cover-branching-mass-is-quantized-by-deck-group: that is a lower bound on the branching mass of symmetric covers; this is an existence obstruction, independent of mass, which rules out every branched cover at once.
  sparse-fully-branched-covers-iff-sofic-with-connected-links: that is the repaired equivalence; this is the lemma which shows its link hypothesis is necessary for items 2 and 3 and costs item 1 nothing.
---

**ESTABLISHED** (proof: `finite-branched-covers-force-connected-vertex-links-proof`).

**Setting.**  Finite branched covers `p: X -> Y` are as in
`sparse-branched-covers-with-sofic-pi1-give-sofic-lattice`: `X` is a finite
2-complex, `p` sends each closed cell isometrically onto a closed cell, and
for every vertex `x` the map `Lk(x) -> Lk(p x)` is a covering of finite
graphs of degree `d_x >= 1` with `Lk(x)` connected.  "Of degree `d_x`" means
every point of `Lk(p x)` has exactly `d_x` preimages, so link coverings are
onto.  (Lemma 1 of `sparse-branched-covers-sofic-pi1-reduction-proof`, that
the star of a degree-1 vertex maps isomorphically, and the definition of
`B` and `beta` use exactly this reading.)

**Theorem.**  Let `Y` be a finite connected 2-complex which is not a single
point.
1. If `Y` admits a finite branched cover by a nonempty `X`, then `p` is onto
   and every vertex link of `Y` is nonempty and connected.
2. Let `W` be two closed unit squares glued at one corner `c`.  Then `W` is a
   finite connected piecewise Euclidean 2-complex with one shape, locally
   CAT(0), contractible (so `pi_1(W) = 1` is sofic), and `W` admits no finite
   branched cover at all.
3. The same holds for `Y' = Y_1^2` with a unit square glued at a corner to a
   vertex: `Y'` is locally CAT(0), `pi_1(Y') = pi_1(Y_1^2)`, it has the same
   infinite simple finite residual `K`, and it has no finite branched cover.

## Consequences

* `branched-cover-monodromy-reduction-without-connected-links` is false:
  the Step 4 construction would turn a sofic model of `pi_1(W) = 1` into a
  finite branched cover of `W`, and there is none.
* Part 2 ("necessity of sparse branching") of
  `sparse-branched-covers-with-sofic-pi1-give-sofic-lattice` is false as
  stated, with `W` as the countermodel.  Parts 1 and 3 are untouched (for
  `W` they are vacuous).  Part 2 holds once every vertex link of `Y` is
  connected; that is verified in
  `sparse-fully-branched-covers-iff-sofic-connected-links-proof`,
  Step B0.
* In `sparse-fully-branched-covers-iff-sofic-simple-residual`, items 2 and 3
  each imply that every vertex link is connected.  For `Y'` they fail while
  item 1 is the open `titz-witzel-kernel-sofic`, so that claim as stated
  implies `titz-witzel-kernel-nonsofic`
  (route `titz-witzel-kernel-nonsofic-from-unrestricted-cover-equivalence`).

DERIVATION
finite-branched-covers-force-connected-vertex-links-proof
