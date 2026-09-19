---
rg: 2
id: packet-controller-orbit-orientation-proof
kind: route
title: Compare controller exponent with the determinant character
target: packet-controller-orbit-products-have-orientation-dichotomy
requires: []
---

In the irreducible `ell^r`-dimensional Weyl packet, every packet generator
has determinant one under the hypotheses in the target.  A rank-one
`ell`-phase controller has determinant `zeta`.  After tensoring with an
arbitrary multiplicity orientation `V`, a product of packet conjugates with
total exponent `k` is the corresponding label product tensored with `V^k`.

If `k=0 mod ell`, the multiplicity term is one for every `V`, so the row is
orientation-blind.  If `k!=0 mod ell`, determinants of the label equality
would give `zeta^k=1`, a contradiction.  This proves the exact dichotomy.
