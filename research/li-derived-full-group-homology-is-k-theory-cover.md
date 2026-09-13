---
rg: 2
id: li-derived-full-group-homology-is-k-theory-cover
kind: claim
title: Li's theorem that derived full group homology is the homology of the universal cover of the groupoid K-theory infinite loop space
artifacts:
  - research/artifacts/full-group-homology-fp-obstruction-2026-09-13.md
---

**ESTABLISHED (import).** Xin Li, arXiv:2209.08087.

**Setting.**
- `G` is an ample groupoid with locally compact Hausdorff unit space.
- `F(G)` is its topological full group, and `D(G)` the commutator subgroup of `F(G)`.
- `K(B_G)` is Li's algebraic K-theory spectrum of the small permutative category `B_G` of
  compact open bisections.
- `S` is the sphere spectrum.

**Statements.**
1. For every abelian group `C`, `H~_*(K(B_G); C) ≅ H_*(G; C)`.
2. If in addition the unit space has no isolated points, and `G` is minimal and has comparison,
   then `H_*(D(G); C) ≅ H_*(Ω~^∞_0 K(B_G); C)` for all `C`. Here `Ω~^∞_0` is the universal cover
   of the base-point component of `Ω^∞ K(B_G)`.
3. The Atiyah–Hirzebruch spectral sequence `E^2_{p,q} = H~_p(K(B_G); π_q(S))` is
   first-quadrant and converges to `π_{p+q}(K(B_G))`.
4. **Recorded examples.**
   - `H_*(Γ ⋉ X; C) ≅ H_*(Γ; C_c(X, C))`.
   - Free actions of countably infinite groups of subexponential growth on compact metrizable
     totally disconnected spaces have comparison.
   - Tiling groupoids of aperiodic repetitive FLC tilings are minimal, with Cantor unit space and
     comparison.
   - The classical Penrose tiling groupoid has `H_0 = Z^8`, `H_1 = Z^5`, `H_2 = Z`, and
     `H_k = 0` for `k >= 3`.

**Scope.** Li draws no finite presentation consequence. The consequences for finite presentation
are `derived-full-group-h2-filtered-by-mod-two-groupoid-homology` and its descendants.

Proof: `li-derived-full-group-homology-citation`.
