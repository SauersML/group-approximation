---
rg: 2
id: sl3-double-one-near-vertex-forces-joint-near-exactness
kind: claim
title: One near-exact vertex of the SL3 arithmetic double forces the other vertex near the same exact representation
artifacts:
  - research/artifacts/sl3-double-one-vertex-anchor-2026-08-21.md
distinct_from:
  sl3-arithmetic-double-near-exact-vertices-fold-projectively: that assumes both vertex restrictions are near exact and folds them; this proves that one near-exact vertex automatically supplies the missing exactness of the other.
  sl3z-regular-microstates-are-congruence-correctable: that asks to correct every regular lattice microstate; this uses the amalgamating relations and assumes one ambient A-vertex is already near exact.
  sl3-regular-arithmetic-double-fold-mark-collapse: that asks for collapse with no near-exact vertex; this removes precisely the one-vertex-outlier sector and leaves only simultaneous two-vertex outliers.
---

Let

```text
C=SL_3(Z),   A=SL_3(Z[1/2]),   D=A *_C A,
h=diag(2,1,1/2).
```

Fix finite presentations and generating sets.  There is a dimension-free
modulus `omega(t)->0` with the following property.  Suppose `sigma` is a
unitary assignment for `D` of defect at most `delta`, with vertex
restrictions `pi_0,pi_1`.  If an exact finite-dimensional representation
`alpha:A->U(d)` satisfies

```text
max_(x in S_A)||pi_0(x)-alpha(x)||_2 <= epsilon,
```

then

```text
max_(x in S_A)||pi_1(x)-alpha(x)||_2
 <= omega(delta+epsilon).                                  (OVA1)
```

The same holds with the vertices reversed.  Consequently a canonical-trace
microstate enemy for the arithmetic-double fold can never have exactly one
near-exact vertex.  Combined with
`sl3-arithmetic-double-near-exact-vertices-fold-projectively`, either the
fold mark collapses or BOTH vertex restrictions stay a uniform distance
from every exact finite-dimensional representation along a subsequence.

This is not Hilbert--Schmidt stability of `A`.  It is an anchored relative
statement: the already exact vertex and the amalgam identify the second
vertex on `C`.  Canonical regularity alone supplies no such initial anchor.

