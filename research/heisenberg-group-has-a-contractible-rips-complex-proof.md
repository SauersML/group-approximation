---
rg: 2
id: heisenberg-group-has-a-contractible-rips-complex-proof
kind: route
title: Extend the orbit map affinely to H_3(R), certify the vertex link by exact arithmetic, and upgrade the local homeomorphism to a homeomorphism by properness
target: heisenberg-group-has-a-contractible-rips-complex
requires:
  - group-rips-complexes-are-cayley-graph-flag-complexes
artifacts:
  - research/artifacts/heisenberg-contractible-rips-2026-09-16.md
---

The full proof is in the artifact. Let `K = Flag(Cay(H,S))` and let `L` be
the link of the vertex `1`. Then `L` is the flag complex of the graph on `S`
with `s ~ s'` iff `s^-1 s' ∈ S`.

1. **Affine equivariant map.** Left multiplication by `g = (p,q,r)` on
   `H_3(R) = R^3` is the affine map `A_g(a,b,c) = (a+p, b+q, c+r+pb)`. So
   the map `f : |K| -> R^3` that is the identity on vertices and affine on
   simplices satisfies `f ∘ L_g = A_g ∘ f`. The action of `H` on `R^3` is
   free and properly discontinuous.
2. **Finite certificate at `1`.** Exact integer arithmetic in
   `experiments/heisenberg-contractible-rips-2026-09-16/search_h3_rips.py verify`
   checks the following.
   - (L1) There is no 4-clique in the link graph, so `dim K = 3`.
   - (L2) `L` is a closed connected surface with `V = 14`, `E = 36`,
     `F = 24` and `χ = 2`, so it is a 2-sphere.
   - (L3) Every link triangle has determinant `±1`. Across every link edge
     the two opposite vertices lie on opposite sides of the plane through `0`
     and the edge.
   - (L4) One generic ray meets exactly one open cone over a link triangle.

   All 24 triangles and their determinants are listed in the artifact, so a
   reader can check them by hand.
3. **Local homeomorphism.**
   - By (L3) the radial projection `|L| -> S^2` is an orientation-preserving
     branched cover. By (L4) it has degree `1`, so it is unbranched and a
     homeomorphism.
   - Hence `f` embeds the closed star of `1` onto a star-shaped neighbourhood
     of `0`.
   - By equivariance, `f` is a local homeomorphism everywhere.
4. **Covering and conclusion.**
   - `H` acts cocompactly on `|K|` with compact fundamental set `St(1)`, and
     properly discontinuously on `R^3`, so `f` is proper.
   - A proper local homeomorphism between locally compact Hausdorff spaces is
     a surjective covering.
   - `|K|` is connected, since `x` and `y` generate `H`, and `R^3` is simply
     connected. So `f` is a homeomorphism.
   - By item 1 of `group-rips-complexes-are-cayley-graph-flag-complexes`,
     `K = R_1(H, d_S)`.

No external theorem beyond point-set topology and degree theory for maps of
closed surfaces is used.
