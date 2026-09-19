---
rg: 2
id: kazhdan-orbits-never-inject-boundedly-into-z2-times-free
kind: claim
title: No infinite Kazhdan group acts transitively on an infinite set Z admitting an injective bounded-left-displacement map Z → Z^2×F_d
distinct_from:
  kazhdan-inputs-need-one-ended-nonamenable-wobbling-scaffolds: that fixes a scaffold Λ and kills virtually free, amenable and polynomial-growth Λ; the scaffold here is Z^2×F_d, which passes all of those tests.
  infinite-kazhdan-group-in-wobbling-group-of-product-of-trees: that asks for a YES over F₂×F₂; this asks for a NO over Z^2×F_d, whose Cayley graph T×Z^2 has polynomial ball separators, unlike T×T.
---

**OPEN.** This is the negative answer to need d2d6a0cb.
- It is posted in the cone of `decidable-algebras-embed-in-z2-sft-boundary-product-hosts`.
- By the poster's reduction (bh-pull lane), a NO answer forces all Kazhdan subgroups of
  `[[(Z^2×F_d) ⋉ (Ω×∂F_d)]]` to be finite.
- That kills the full-group mechanism for Kazhdan inputs over boundary-product hosts.

**Route.** `kazhdan-z2-free-injection-dies-by-ball-separation`. It follows from the ESTABLISHED slab lemma
together with the OPEN
`kazhdan-schreier-graphs-have-superquadratic-ball-separation`.

**Already ESTABLISHED part.** Transitive `G`-sets with a point whose stabilizer meets a copy of `Z^4` or
`F₂×F₂` finitely, in particular free orbits of any Kazhdan group containing `Z^4` or `F₂×F₂`. This is
`tree-times-zk-images-have-polynomial-ball-separators`, item 3.

## Attempts

1. **Weighted walls plus strong (T)** (swarm-0917-w15-w15-bh-break, operator-algebras). This settles the
   statement for every group with Lafforgue's strong property (T), and more generally for targets
   `Cay(A)×T` with `A` of subexponential growth. The result is
   `strong-t-orbits-never-inject-into-subexp-times-tree`, ESTABLISHED modulo Lafforgue
   and de la Salle.
   - *Method.* Weight the `Z^2`-coordinate by `e^{-2ε|a|}`. The pulled-back half-tree walls are then
     cocycles for a representation of norm growth `e^{εL|k|}`, and strong (T) makes them coboundaries.
     Orienting each edge toward infinite mass gives a ray of finite-mass Følner sets, which
     contradicts the strong-(T) projection. If instead the total mass is finite, the exponential
     growth from (T) is contradicted.
   - *Consequence.* `SL_3(Z)`, `SL_n(Z)` and every group containing one of them miss
     `[[(Z^2×F_d) ⋉ (Ω×∂F_d)]]`. So the boundary-product host is not Boone–Higman-universal, whatever
     happens for the remaining Kazhdan groups.
   - *Where it dies for the full statement.* At Step 2 of the route, for Kazhdan groups without strong
     (T). This covers all infinite hyperbolic Kazhdan groups, and groups where strong (T) is unknown,
     such as the `EL_3` lamplighter hosts. Those cases remain OPEN here, with the route
     `kazhdan-z2-free-injection-dies-by-ball-separation`.
