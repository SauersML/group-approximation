---
rg: 2
id: simple-triangle-quotientless-from-non-vtf-triangle
kind: route
title: Amalgamating a non-virtually-torsion-free hyperbolic triangle into alternating groups gives a quotientless simple-vertex triangle
target: hyperbolic-simple-triangle-group-without-finite-quotients
requires: [hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free, simple-vertex-triangles-are-universal-for-triangle-vtf]
---

Take the triangle `T°` supplied by the premise, with vertex groups `B_v`. Replace each
`B_v` by `A_v = Alt(|B_v| + 2)`, through the regular representation followed by the
sign-corrected inclusion `Sym(m) -> Alt(m+2)`. Keep the edge groups.

By (U1) the half-girths do not change, so the new triangle is hyperbolic. It has finite
simple vertex groups, nontrivial edge groups and trivial face group. By (U4) its colimit
has a nontrivial finite quotient only if `Λ(T°)` has a finite quotient injective on
every `B_v`. The premise excludes that. This is (U5) (a) => (b) of
`simple-vertex-triangles-are-universal-for-triangle-vtf`.
