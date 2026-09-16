---
rg: 2
id: heisenberg-group-has-a-contractible-rips-complex
kind: claim
title: The integral Heisenberg group has a scale-1 Rips complex homeomorphic to R^3, for the generating set x, y, z, xz, yz, xy, xyz and inverses
distinct_from:
  every-type-f-group-has-a-contractible-rips-complex: that is the universal affirmative answer to Zaremsky Problem 4.7; this settles only the integral Heisenberg group, with an explicit generating set
  virtually-abelian-groups-have-contractible-rips-complexes: that covers virtually abelian groups; H_3(Z) is nilpotent of class 2 and not virtually abelian
  linf-preserving-proper-actions-give-contractible-rips: that needs affine actions with signed-permutation linear parts; left translation on H_3(R) has unipotent linear parts [[1,0,0],[0,1,0],[0,p,1]], which are not signed permutations
  baumslag-solitar-groups-have-contractible-rips-complexes: that triangulates a 2-dimensional one-relator complex for BS(m,n); this is a 3-dimensional affine triangulation of Nil for H_3(Z)
artifacts:
  - research/artifacts/heisenberg-contractible-rips-2026-09-16.md
---

Let `H = H_3(Z)` be the set of triples `(a,b,c) ∈ Z^3` with multiplication
`(a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab')`. Put `x = (1,0,0)`,
`y = (0,1,0)` and `z = (0,0,1) = [x,y]`. Let

`S = {x, y, z, xz, yz, xy, xyz}^±1`,

where `{x, y, z, xz, yz, xy, xyz} = {(1,0,0), (0,1,0), (0,0,1), (1,0,1),
(0,1,1), (1,1,1), (1,1,2)}`. So `|S| = 14`.

**Claim.** The clique complex `Flag(Cay(H,S))` is homeomorphic to `R^3`. It
is the Rips complex `R_1(H, d_S)`, which is therefore contractible.

More precisely, send each vertex `(a,b,c)` to the point `(a,b,c) ∈ R^3` and
extend affinely over simplices. The resulting map is an `H`-equivariant
homeomorphism onto `H_3(R) = R^3`, where `H` acts on `R^3` by left
multiplication. The complex is 3-dimensional, and each vertex link is a
triangulated 2-sphere with 14 vertices and 24 triangles.

**Why it matters here.** `some-type-f-group-has-no-contractible-rips-complex`
names the integral Heisenberg group, together with `BS(1,2)`, as a test
object: a group of type F with distorted infinite cyclic subgroups. With
`baumslag-solitar-groups-have-contractible-rips-complexes`, this rules out
both named test objects. The following cannot by themselves obstruct a
contractible Rips complex:
- polynomially distorted central subgroups;
- a cubic Dehn function;
- nilpotency without virtual abelianness.

No source stating this result was found in the 2026-09-16 literature gate. It
may nevertheless be known.
