---
rg: 2
id: nonhyperlinear-from-canonical-iwahori-projection-transfer
kind: route
title: Cut the HNN stable letter to a positive-density Iwahori projection carrier
target: non-hyperlinear-group
requires:
  - sl2-z-same-dimension-hs-stable
  - iwahori-transfer-failure-reduces-to-two-block-projection
  - iwahori-transfer-failure-has-two-positive-density-blocks
  - canonical-iwahori-projection-commutant-transfer
---

Let

```text
A=SL_2(Z[1/2])=C_+ *_(B_+=B_-) C_-,
G=<A,t | [t,C_+]=1>,
w=[t,a],                         a in C_-\B_-.
```

Britton's lemma gives `w!=1`.  If `G` were hyperlinear, take canonical-trace
matrix microstates.  Same-dimension HS stability of each `SL_2(Z)` vertex
rounds the two vertex restrictions to exact representations without changing
the edge defect or the canonical trace condition `(CIP1)`.  The stable-letter
unitaries asymptotically commute with the first vertex, while canonical
separation of `w` says that their commutator with the fixed second-vertex word
`a` stays macroscopic.

The two-block dilation produces positive-density projections satisfying
`(CIP2)` but violating `(CIP3)`.  This contradicts
`canonical-iwahori-projection-commutant-transfer`.  Hence `G` is
nonhyperlinear.

This route consumes only the regular-character sector actually present in a
hyperlinearity contradiction.  It does not assume a modulus for arbitrary
finite-dimensional characters and does not perturb the full amalgam to an
exact representation.
