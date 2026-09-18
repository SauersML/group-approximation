---
rg: 2
id: two-dimensional-cat0-hyperbolic-groups-virtually-torsion-free
kind: claim
title: Every hyperbolic group acting properly and cocompactly on a CAT(0) piecewise Euclidean 2-complex is virtually torsion-free
distinct_from:
  hyperbolic-groups-virtually-torsion-free: that is the root question for all hyperbolic groups; this is the positive assertion for the 2-dimensional CAT(0) class, which is exactly the hypothesis (V2) consumed by sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers
  hyperbolic-finite-residual-is-torsion-free: that is the unrestricted positive assertion and implies this one; this is its restriction to groups with a proper cocompact action on a CAT(0) 2-complex, the class containing all hyperbolic polygons and triangles of finite groups
  hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free: that asks for a counterexample among triangles of finite groups, all of which lie in this class; a single one refutes this claim
---

**OPEN.** The claim: let `Γ` be word-hyperbolic, acting properly, cocompactly
and by cellular isometries on a CAT(0) piecewise Euclidean 2-complex with
finitely many shapes. Then `Γ` has a torsion-free subgroup of finite index.

**Why it matters here.** This is hypothesis (V2) of
`sofic-lattice-plus-hyperbolic-vtf-gives-flat-hitting-covers`. With soficity of
`pi_1(Y_1^2)`, it yields `titz-witzel-flat-hitting-sparse-branched-covers`
(route `titz-witzel-flat-hitting-via-soficity-and-2d-vtf`). The groups it is
applied to are orbihedral fundamental groups:
* the vertex groups are finite, `pi_1(Lk)/N`, over a sofic-model cover;
* edge and face groups are trivial.

**What is known.**
* It follows from `hyperbolic-finite-residual-is-torsion-free`, through
  `finite-torsion-carrier-virtual-torsionfree-criterion` (route
  `two-dimensional-cat0-hyperbolic-vtf-via-finite-residual`).
* Wise (Invent. Math. 149 (2002), Thms 9.1 and 9.3, as recorded in
  `hyperbolic-triangle-of-finite-groups-not-virtually-torsion-free`) proves
  residual finiteness, hence virtual torsion-freeness, for polygons of finite
  groups with at least 6 sides and some 4- and 5-gons.
* Triangles of finite groups are open. A hyperbolic triangle of finite groups
  that embeds in no finite group would refute this claim.

## Attempts

* **2026-09-17 (swarm-0917-w8): restrict to the orbihedra actually used.**
  The groups needed by `sofic-plus-vtf-flat-hitting-covers-proof` are developments
  of complexes of groups over a finite 2-complex. Their vertex groups
  `pi_1(Lk)/N` are finite, their edge and face groups are trivial, and the
  branch vertices are isolated. One would like to build the torsion-free
  finite-index subgroup by hand. Take finite covers of the underlying cover
  `X_n` that unwrap each `L_x -> L'_x` compatibly.

  This dies at the global compatibility step. It requires a finite cover of the
  complement `X_n \ S` whose restriction to every link of a point of `S` is the
  chosen cover `L'_x`. That is a separability statement for the peripheral
  structure, of exactly the strength of the claim itself. The obvious
  alternative is to go through Wise's polygon theorems. That route dies because
  the complexes here are triangle complexes, with vertices of degree 45 and
  more; they are not polygons of finite groups with at least 6 sides.
