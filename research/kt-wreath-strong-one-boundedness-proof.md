---
rg: 2
id: kt-wreath-strong-one-boundedness-proof
kind: route
title: Compose the Kun--Thom lamp Cartan with the Jung--Hayes entropy ceiling
target: kt-wreath-hyperlinearity-forces-strong-one-boundedness
requires:
  - kt-wreath-algebra-has-a-lamp-cartan
  - cartan-algebras-are-strongly-one-bounded
---

`kt-wreath-algebra-has-a-lamp-cartan` gives, for `q = 2`, a separable II_1
factor `L(W)` with the diffuse hyperfinite regular masa `L^infinity(X)`.
`cartan-algebras-are-strongly-one-bounded` (Jung GAFA 2007; Hayes IMRN 2018,
Theorem 3.8 and Property 1, source-verified in that node) gives
`h(L(W)) <= h(L^infinity(X)) = 0`.  Strong 1-boundedness and `delta_0 <= 1`
follow when microstates exist, and `h = -infinity` otherwise.

The remark in the target about the double uses Hayes' Property 3 (joins over
diffuse intersections), recorded as verified in
`cartan-algebras-are-strongly-one-bounded`, and property-(T) strong
1-boundedness (Hayes--Jekel--Kunnawalkam Elayavalli, arXiv:2107.03278, cited in
`coset-wreath-hyperlinearity-forces-strong-one-boundedness`).  That remark is
not needed for the target's displayed statement.
