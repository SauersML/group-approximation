---
rg: 2
id: sl2-root-kazhdan-quotientless-member-kazhdan-instance
kind: route
title: A quotientless Kazhdan SL_2 root triangle is an infinite hyperbolic Kazhdan group without finite quotients
target: kazhdan-hyperbolic-group-without-finite-quotients
requires: [sl2-root-kazhdan-triangle-without-finite-quotients, kazhdan-hyperbolic-sl2-root-triangles]
---

Let `Λ` be a colimit from `sl2-root-kazhdan-triangle-without-finite-quotients` with no nontrivial finite
quotient. By `kazhdan-hyperbolic-sl2-root-triangles`:
- (K2): `Λ` is infinite and word-hyperbolic;
- (K3): `Λ` has property (T).

By assumption every homomorphism from `Λ` to a finite group is trivial. So `Λ` is the group demanded by
`kazhdan-hyperbolic-group-without-finite-quotients`.
