---
rg: 2
id: nonhyperlinear-via-leavitt-singular-near-state
kind: route
title: Exclude the only possible Leavitt near-state witness
target: non-hyperlinear-group
requires:
  - binary-leavitt-hyperlinear-iff-singular-near
  - binary-leavitt-has-no-purely-singular-free-near-representation
---

Let `Q=L_(F_2)(1,2)^x`.  The equivalence
`binary-leavitt-hyperlinear-iff-singular-near` says that `Q` is hyperlinear
exactly when it admits a purely singular essentially free state-form near
representation.  The second dependency excludes precisely such a witness.
Hence `Q` is not hyperlinear, furnishing the explicit group required by the
target.
