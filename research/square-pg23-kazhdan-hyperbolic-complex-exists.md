---
rg: 2
id: square-pg23-kazhdan-hyperbolic-complex-exists
kind: claim
title: A finite square complex with PG(2,3) links has a Kazhdan hyperbolic fundamental group with b_2 at least one
refuted_by:
  - square-pg23-groups-cannot-be-kazhdan
distinct_from:
  kazhdan-two-complex-b2-is-euler-characteristic-minus-one: that is the proved b_2 and hyperbolicity computation for any such complex; this asserts that a finite complex of that shape exists and has property (T), inputs taken from the literature that are not yet source-verified here
  torsion-free-hyperbolic-kazhdan-partner-exists: that is an established existence theorem for some hyperbolic Kazhdan group with no Betti number information; this pins an explicit shape whose b_2 is computable from the vertex count
---

**REFUTED.** There is a finite connected square
complex `K` with at least two vertices, all corner angles `π/3` in the hyperbolic
metric, and every vertex link isomorphic to the incidence graph of `PG(2,3)`, such
that `Γ = π_1(K)` has property (T).

Given this, `kazhdan-two-complex-b2-is-euler-characteristic-minus-one` makes `Γ` an
explicit torsion-free hyperbolic Kazhdan group with `b_2(Γ) = |V| - 1 >= 1`. That is
a pinned candidate for `kazhdan-hyperbolic-b2-group-flexibly-hs-stable`.

## Why the proposed candidate fails

Assigning Euclidean unit squares gives the same complex a locally CAT(0)
cubical metric. The free deck action and Niblo--Reeves's Kazhdan fixed-point
theorem force a Kazhdan fundamental group to be trivial, contradicting
`χ(K) = |V| >= 2`. The refuting claim includes a complete proof.

The previous attempt applied the simplicial link-gap threshold directly
to square links. That is invalid. Coning the squares to their centers
subdivides each old link, and its actual normalized spectral gap becomes
`1 - sqrt((4 + sqrt(3))/8) < 1/2`. Thus the earlier gap computation on the
unsubdivided incidence graph cannot certify (T). Whether the underlying
finite complexes exist without (T) is immaterial to the refutation.
