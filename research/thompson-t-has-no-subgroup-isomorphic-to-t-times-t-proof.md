---
rg: 2
id: thompson-t-has-no-subgroup-isomorphic-to-t-times-t-proof
kind: route
title: T x T contains a Klein four-group while T has only cyclic finite subgroups
target: thompson-t-has-no-subgroup-isomorphic-to-t-times-t
requires:
  - finite-subgroups-of-thompson-t-are-cyclic
---

The rotation `r(x) = x + 1/2 mod 1` of the circle is in `T`: it is linear with
slope 1 and preserves the dyadic rationals. It has order 2. So `T × T`
contains the subgroup `<(r, 1), (1, r)> ≅ Z/2 × Z/2`, which is finite and not
cyclic. An injective homomorphism `φ : T × T → T` would map it isomorphically
onto a non-cyclic finite subgroup of `T`, contradicting
`finite-subgroups-of-thompson-t-are-cyclic`.
