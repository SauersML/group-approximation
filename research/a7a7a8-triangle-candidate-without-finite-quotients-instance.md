---
rg: 2
id: a7a7a8-triangle-candidate-without-finite-quotients-instance
kind: route
title: A quotientless candidate among the four (A_7, A_7, A_8) triangles is an instance of the simple-vertex target
target: hyperbolic-simple-triangle-group-without-finite-quotients
requires: [a7a7a8-triangle-candidate-without-finite-quotients]
---

Each `G_i` meets every requirement of the target class:
- it is the fundamental group of a triangle of groups with finite simple vertex groups
  `A_7, A_7, A_8`;
- its edge groups `Z/7` are nontrivial and its face group is trivial;
- its links have girths `6, 6, 8`, so the half-girth type is `(3,3,4)`. This was computed in GAP in
  `research/artifacts/simple-vertex-triangle-quotient-search-2026-09-12.md` §2.

Then `1/3 + 1/3 + 1/4 < 1`, and Caprace–Conder–Kaluba–Witzel Theorem 3.1(v), as used there, makes
`G_i` infinite and word-hyperbolic. So a `G_i` without nontrivial finite quotients is a
member of the class demanded by `hyperbolic-simple-triangle-group-without-finite-quotients`.
