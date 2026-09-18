---
rg: 2
id: two-dim-cat0-product-groups-are-torsion-locally-finite
kind: claim
title: A group acting with finite point stabilizers on a finite product of 2-dimensional CAT(0) triangle complexes and trees is torsion locally finite, so the finitely presented simple Kac–Moody lattices with 2-dimensional buildings contain no infinite finitely generated periodic group
distinct_from:
  circle-and-tree-product-periodic-subgroups-are-finite: that handles circle actions and proper actions on finite products of trees (rank-2 Kac–Moody lattices, Burger–Mozes and Wise lattices); this adds 2-dimensional CAT(0) factors through Norin–Osajda–Przytycki, which reaches rank-3 and other 2-dimensional Kac–Moody lattices and lattices in products of Ã2 and Fuchsian buildings.
  almost-automorphism-torsion-subgroups-are-rf: that excludes the Thompson-type Cantor hosts (V, V_{d,r}, Röver–Nekrashevych groups) by a depth-cocycle argument; this excludes a family of finitely presented simple lattices by fixed points in CAT(0) factors.
  fp-simple-kac-moody-lattices-satisfy-pbh: that puts the finitely presented simple Kac–Moody groups and all their subgroups in the permutational Boone–Higman class; this constrains which periodic groups can be among those subgroups when the buildings are 2-dimensional.
artifacts:
  - research/artifacts/gq-bh-bh-lit-survey.md
---

**ESTABLISHED (2026-09-18)** through `two-dim-cat0-product-groups-torsion-lf-proof`. Lane proof (bh-free-12),
elementary given the cited inputs, not independently reviewed. No priority is claimed: the main input is the
Norin–Osajda–Przytycki fixed point theorem, and the extension to products and to non-cocompact lattices is formal.

## Statement

Call a group **torsion locally finite** if every finitely generated torsion subgroup is finite.

1. **General theorem.** Let `X_1, …, X_k` be CAT(0) triangle complexes in the sense of Norin–Osajda–Przytycki
   (arXiv:1902.02457v3, §1: 2-dimensional simplicial complexes with a piecewise smooth Riemannian metric, finitely
   many isometry classes of triangles at each vertex, complete, CAT(0)). Let `Y_1, …, Y_l` be simplicial trees. Let
   `Γ` act by automorphisms on each `X_i` and each `Y_j`, and suppose the stabilizer in `Γ` of every point of
   `X_1 × … × X_k × Y_1 × … × Y_l` is finite. Then `Γ` is torsion locally finite. In particular every finitely
   generated subgroup of `Γ` of finite exponent is finite.
2. **Kac–Moody lattices with 2-dimensional buildings.** Let `A` be a generalized Cartan matrix whose Weyl group `W`
   has no spherical subset of three generators, e.g. every irreducible non-spherical non-affine 2-spherical `A` of
   rank 3. Let `Λ = G_A(F_q)` be the split minimal Kac–Moody group over any finite field. Then `Λ` and `Λ / Z(Λ)` are
   torsion locally finite.
   - For 2-spherical, indecomposable, non-spherical, non-affine `A` and `q > 1764^n`, `Λ/Z(Λ)` is finitely presented,
     simple and Kazhdan (`simple-kazhdan-kac-moody-lattices-exist`).
   - For example `Λ_(2,4,6)(q)`, `q > 1764^3`, is a finitely presented simple Kazhdan group in which every finitely
     generated torsion subgroup is finite.
3. **Other hosts covered.** Every group acting with finite point stabilizers on a finite product of Ã2 buildings,
   Fuchsian (Bourdon) buildings, other 2-dimensional Euclidean or hyperbolic buildings, and trees, is torsion locally
   finite. This includes exotic and arithmetic Ã2 lattices, lattices in products of such buildings, and non-uniform
   lattices.
4. **For Boone–Higman.** None of these groups contains an infinite finitely generated periodic group: no infinite free
   Burnside group, no Tarski monster, no Grigorchuk group. So they are not witnesses for
   `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup`, nor hosts for
   `free-burnside-groups-satisfy-boone-higman`.

## Scope

- The finitely presented simple Kac–Moody lattices whose buildings have dimension `>= 3` (a spherical triple in `W`)
  are **not** covered. For them the needed fixed point theorem is Norin–Osajda–Przytycki's Conjecture 1.5 ("every
  finitely generated group acting without a global fixed point on a finite-dimensional CAT(0) complex contains an
  element of infinite order"). The conjecture is known for CAT(0) cube complexes (Sageev) and open in general.
- Finite dimension matters. NOP (§1) note that Burnside groups act without global fixed point on
  infinite-dimensional CAT(0) cube complexes (Osajda 2018).
