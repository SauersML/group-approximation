---
rg: 2
id: ghb7-congruence-kernel-b2-euler-count-proof
kind: route
title: Free action of the vertex-injective kernel on the CAT(−1) triangle complex, cell count, Euler characteristic
target: ghb7-congruence-kernel-hyperbolic-kazhdan-with-large-b2
requires: [cckw-ghb2-kms-group-structure]
---

## Proof

Write `G = G_{HB_2}(7)`, `X_0 = <a,b>`, `X_1 = <c,b>`, `X_2 = <c,a>`, and `H = Ker(ψ)`.

1. **Torsion-free finite index.** `ψ` is injective on each `X_i`
   (`cckw-ghb2-kms-group-structure`, item 5). By item 4, `H` is torsion-free of finite
   index.
2. **Free cocompact action.** `G` acts on the CAT(−1) 2-complex `Y` with a triangle as
   strict fundamental domain (item 3).
   - Stabilizers: trivial on triangles, `<a>, <b>, <c>` (order `7`) on edges, and the
     `X_i` on vertices. Every simplex stabilizer is a conjugate of a subgroup of some
     `X_i`.
   - Freeness: `H` is normal and `ψ` is injective on `X_i`, so `H ∩ gX_ig^{-1} = 1`.
   - Cocompactness: `H` has finite index and `G` acts cocompactly.
3. **Asphericity.** `Y` is CAT(0), hence contractible. So `H\Y` is a finite 2-dimensional
   `K(H,1)` and `b_k(H;Q) = 0` for `k >= 3`.
4. **Cell count.** `G/H` acts on `H\Y`. The `H`-orbits in the `G`-orbit of a simplex `σ`
   are the cosets of the image of `G_σ` in `G/H`. That image is isomorphic to `G_σ`,
   since `G_σ ∩ H = 1`, so the `G`-orbit of `σ` gives `[G:H]/|G_σ|` cells:

   ```text
   vertices   [G:H]·(1/343 + 1/2401 + 1/2401)
   edges      [G:H]·(1/7 + 1/7 + 1/7)
   triangles  [G:H]
   ```

   So `χ(H\Y) = [G:H]·(9/2401 − 1029/2401 + 2401/2401) = [G:H]·1381/2401`.
5. **First Betti number.** `G` has property (T) (item 1), so its finite-index subgroup
   `H` does, and `H` has finite abelianization: `b_1(H;Q) = 0`.
6. **Second Betti number.** `b_2(H;Q) = χ(H) − 1 = [G:H]·1381/2401 − 1`.
7. **Index bound.** `[G:H] = |ψ(G)|`, and `ψ(X_1)` has order `2401`, so `2401 | [G:H]`.
   So `b_2(H;Q) >= 1381 − 1 = 1380`.
8. **Hyperbolicity.** `G` is word-hyperbolic (item 1, or item 3 through Švarc--Milnor),
   so its finite-index subgroup `H` is too.

**For `G` itself.** `G` acts properly with finite stabilizers on contractible `Y`, so
`H^*(G;Q) = H^*(G\Y;Q)`. The quotient is a triangle, so `b_2(G;Q) = 0`.

∎
