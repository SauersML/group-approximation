---
rg: 2
id: matrix-corona-rank-germs-absorb-fixed-depth-leavitt-escape
kind: claim
title: Nonzero matrix-corona rank germs absorb every fixed orbit and divisibility depth
distinct_from:
  surviving-leavitt-corona-character-has-infinite-parabolic-orbit: that derives arbitrarily many orthogonal equivalent translates from a surviving character atom; this proves that all resulting fixed-multiplicity inequalities are compatible with one nonzero corona projection.
  matrix-corona-projection-monoid-is-rank-germs: that classifies the whole projection monoid and proves literal D equals 2D collapses; this exhibits a nonzero germ which is divisible at every separately fixed depth without satisfying D equals 2D.
  maximal-sparse-character-atom-does-not-return-multiplicity: that identifies moving exact character refinements as the escape; this gives the projection-monoid normal form of that escape.
artifacts:
  - research/matrix-corona-fixed-depth-leavitt-escape-proof.md
---

There is a norm matrix corona `Q_d` and a nonzero projection class `a` in
`V(Q_d)` such that both of the following hold:

```text
M a <= [1]                 for every fixed M>=1,          (FDL1)
a = 2^N b_N               for every fixed N>=1           (FDL2)
```

for suitable nonzero projection classes `b_N` depending on `N`.

Thus neither an infinite family of orthogonal equivalent translates in the
ambient identity nor divisibility through every separately fixed binary
prefix depth contradicts stable finiteness.  The cancellation theorem uses
the same class on both sides of one exact equation `a=2a`.  Replacing its
right-hand occurrence by a depth-dependent finer class is not enough.

For the Property-T-free binary-Leavitt corona route this is sharp: parabolic
orbit growth plus all fixed-depth multiplicity refinements cannot replace a
same-reservoir return.  A successful projection/K-zero proof must produce a
finite closed supercritical branching system on fixed classes, or an actual
partial isometry from one marked carrier onto two orthogonal subprojections
of that same carrier.

