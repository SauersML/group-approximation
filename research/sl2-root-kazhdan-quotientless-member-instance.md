---
rg: 2
id: sl2-root-kazhdan-quotientless-member-instance
kind: route
title: A quotientless Kazhdan SL_2 root triangle is a member of the simple-vertex hyperbolic triangle target
target: hyperbolic-simple-triangle-group-without-finite-quotients
requires: [sl2-root-kazhdan-triangle-without-finite-quotients, kazhdan-hyperbolic-sl2-root-triangles]
---

Let `Λ` be a colimit from `sl2-root-kazhdan-triangle-without-finite-quotients` with no nontrivial finite
quotient. By `kazhdan-hyperbolic-sl2-root-triangles` (K1), (K2), its triangle of groups has:
- finite simple vertex groups `SL_2(q), SL_2(q), SL_2(q^2)`;
- nontrivial edge groups `(Z/2)^f` and trivial face group;
- half-girths `(3, 3, >= 5)`, so the Gersten–Stallings angle sum is at most
  `π/3 + π/3 + π/5 < π`.

That is exactly the data demanded by `hyperbolic-simple-triangle-group-without-finite-quotients`, and
`Λ` has no nontrivial finite quotient.
