---
rg: 2
id: sofic-sl3-action-two-outlier-proof
kind: route
title: Restrict the sofic free-wreath models and apply the one-vertex anchor contrapositive
target: sofic-sl3-vertex-action-produces-two-outlier-double-models
requires:
  - sl3-regular-double-collapse-forces-nonsofic-vertex-action
  - sl3-double-one-near-vertex-forces-joint-near-exactness
  - sl3-arithmetic-double-near-exact-vertices-fold-projectively
---

The first prerequisite constructs canonical permutation microstates of the
double from a sofic model of `A action A/C`; their nontrivial fold word has
trace tending to zero.

If `(SOM1)` failed, pass to a subsequence on which one vertex approaches an
exact representation.  The one-vertex anchor corrects the other vertex to
the same representation.  Joint near-exact projective folding then makes
the fold word's trace modulus tend to one, contradicting its canonical trace
zero.  Therefore the minimum of the two vertex-to-representation distances
has positive liminf.  After one more subsequence this gives the common
constant asserted in `(SOM1)` for both vertices.

