---
rg: 2
id: sl3z-euler-fibered-subgroup-gives-bieri-witness
kind: route
title: A fibred two-dimensional subgroup with nonzero Euler characteristic has a non-free fibre, because mapping tori of roses have Euler characteristic zero
target: sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup
requires:
  - sl3z-contains-cd2-euler-positive-fibered-subgroup
artifacts:
  - research/artifacts/sl3z-normal-f2-obstruction-2026-09-16.md
---

Let `G <= SL_3(Z)` be of type FP with `cd G = 2` and `χ(G) != 0`, and let
`φ: G -> Z` be onto with finitely generated kernel `K`.

- `G` is finitely generated, because it is of type FP.
- `G` is torsion-free, because its cohomological dimension is finite.
- `K ◁ G` has infinite index, because `G/K ≅ Z`.

**`K` is not free.** Suppose `K ≅ F_r`. The rank `r` is finite because `K` is
finitely generated, and `G ≅ F_r x|_ψ Z` for an automorphism `ψ`.

- Realize `ψ` by a cellular homotopy equivalence `f` of the rose `R_r` with one
  vertex and `r` edges, and let `T` be its mapping torus.
- `T` is aspherical: it is a graph of spaces over a circle with vertex and
  edge space `R_r`, and both attaching maps are `π_1`-injective. Also
  `π_1(T) ≅ G`.
- The cells of `T` are the cells `e` of `R_r` and the products `e x (0,1)`.
  So `χ(T) = χ(R_r) - χ(R_r) = 0`.
- For `G` of type FP, `χ(G) = Σ_k (-1)^k dim_Q H_k(G; Q)` equals the cellular
  Euler characteristic of any finite `K(G, 1)`. So `χ(G) = χ(T) = 0`, a
  contradiction.

So `K` is finitely generated, not free, and of infinite index in `G`, and
`(G, K)` witnesses `sl3z-contains-cd2-group-with-fg-nonfree-normal-subgroup`.

The fibred criterion is therefore a special case of the Bieri-type criterion.
The dimension count does not use `SL_3(Z)`.
