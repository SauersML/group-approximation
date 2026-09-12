---
rg: 2
id: culf-mastel-rstar-commutativity-row-peeling-proof
kind: route
title: Read the two fresh coordinates in Proposition 6.2 as a peelable tail
target: culf-mastel-rstar-commutativity-replacement-rows-peel-off
requires:
  - rstar-two-tail-peeling-reduces-fc-char-to-a-dense-kernel
  - culf-mastel-rstar-reduction-is-support-blind
---

Proposition 6.2 starts with a two-variable empty constraint `V_i={x,y}`.
For every other position `w` of the chosen non-TVF relation it introduces a
new variable `z_(i,w)` indexed by that occurrence.  With `R_*` there are
exactly two such positions.  Neither new variable occurs in another row, so
both have degree one before any peeling.  The first prerequisite deletes the
row and reconstructs it through a maximal cap while retaining `x,y`.

Theorem 6.8 applies Proposition 6.2 only after the pp reduction and
subdivision have produced a `CSP(R_*)` instance with empty two-variable
constraints.  Hence removing these leaf rows exposes, but does not alter,
the kernel of the pre-existing nonempty `R_*` rows.

