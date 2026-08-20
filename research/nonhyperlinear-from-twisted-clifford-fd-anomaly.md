---
rg: 2
id: nonhyperlinear-from-twisted-clifford-fd-anomaly
kind: route
title: Combine the injective Clifford HNN with its finite-dimensional HS anomaly
target: non-hyperlinear-group
requires:
  - twisted-clifford-substitution-endomorphism-gate
  - twisted-clifford-substitution-has-tensor-stable-fd-anomaly
---

The endomorphism gate gives a finitely presented ascending HNN group and, by
Britton normal form, a nontrivial central sign `J`.  If the group were
hyperlinear, its canonical trace would have finite-dimensional microstates in
which all presentation relator energies tend to zero while the nonidentity
involution `J` stays at normalized-HS distance tending to `sqrt(2)` from the
identity.  This contradicts the tensor-stable anomaly for any fixed
`alpha<sqrt(2)`.  Hence the explicit HNN group is non-hyperlinear.
