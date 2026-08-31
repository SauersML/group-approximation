---
rg: 2
id: hyperlinear-to-sofic-via-local-holonomy-gauge
kind: route
title: Independently match the unitary colours and express coherent rounding as a local gauge system
target: hyperlinear-implies-sofic
requires:
  - hs-defect-is-mean-square-sphere-displacement
  - spherical-tight-single-colour-near-perfect-matching
  - partial-schreier-completion-preserves-sofic-loss
  - spherical-relation-defect-pairs-small-chord
  - relation-defects-obey-permutation-gauge-law
  - spherical-short-holonomies-admit-local-gauge
  - coherent-reselection-reduces-to-private-label-core
  - trace-separation-sphere-distance-concentration
---

Fix a finite regular-character table and a target Hamming error.  Take a
sufficiently accurate hyperlinear microstate and one sufficiently large iid
spherical cloud.  Choose the label matchings independently at a very small
radius and complete the missing `o(N)` pieces, charging all completion roots
to the error budget.

The mean-square displacement identity makes the unitary relation defects
pointwise small off another `o(N)` set.  Hence
`spherical-relation-defect-pairs-small-chord` makes the two discrete outputs
of each relation a short chord on almost every root.  Because the
`k`-matching has near-total range, all but another `o(N)` of those outputs
lie in its tight range; pulling the chord back through that matching adds only
two matching radii and shows that the holonomy

```text
delta_(g,h,k)=sigma_k^(-1)sigma_g sigma_h
```

moves almost every remaining source point by a radius tending to zero.

Apply `spherical-short-holonomies-admit-local-gauge`.  It gives
geometrically local source corrections `c_s` solving the finite holonomy
system on `1-o(1)` of the roots.  By
`relation-defects-obey-permutation-gauge-law`, the corrected permutations
`tilde_sigma_s=sigma_s c_s` therefore satisfy every tested multiplication
relation in Hamming distance `o(1)`.

The corrected maps still track the original unitary colours: the tracking
error is at most the original matching radius plus the correction chord,
outside the union of the charged exceptional sets.  For distinct tested
words, `trace-separation-sphere-distance-concentration` gives a fixed
geometric gap between the corresponding unitary images on `1-o(1)` of the
cloud.  Choosing the matching and gauge radii below half that gap makes
equality of the corrected word maps impossible there.  Thus the corrected
permutations are asymptotically Hamming-separated as required.

This constructs a sofic model of every finite window conditional on the gauge
claim.  The gauge=reselection equivalence shows that this is not a bypass of
coupled rounding.  The new private-label reduction does, however, prove the
route unconditionally for every Tietze-peelable finite table and reduces the
general window to its nonempty private-label relation core.  Independent Hall
matchings and exact composition solve every peeled relation; the only missing
step is a joint coherent selection theorem on the surviving core.
