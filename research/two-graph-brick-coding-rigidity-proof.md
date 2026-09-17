---
rg: 2
id: two-graph-brick-coding-rigidity-proof
kind: route
title: Kraft equality plus Perron–Frobenius pins the total length cocycle; nonnegativity on cycles and transport kill pure coordinates
target: two-graph-brick-codings-are-rigid-under-rank-two-h1
requires: []
artifacts:
  - research/artifacts/nv-brick-codings-of-two-graphs-2026-09-17.md
---

Full proof: Part B, Steps B1–B6, of the artifact. Outline:

1. **B1.** `ℓ_j = |φ_j|` is a cocycle by (B2), so `L = Σℓ_j` is too, and by (R2)
   `L = αd_1 + βd_2 + δg`. By (B1) the bricks at `a` have total volume 1, which reads
   `M_1 2^{-g} = 2^α 2^{-g}`.
   - A positive eigenvector of an irreducible nonnegative matrix belongs to the spectral
     radius, and that eigenspace is one-dimensional. The constant vector is a positive
     eigenvector for the eigenvalue `N_1`.
   - So `2^α = N_1` and `g` is constant. Code lengths are integers, so `α` is an
     integer. The same holds in colour 2.
2. **B2.** `ℓ_j = α_jd_1 + β_jd_2 + δg_j`, with `Σα_j = α` and `Σβ_j = β`. Summing over a
   colour-`i` cycle gives `α_j, β_j ≥ 0`.
3. **B3.** A rectangle of degree `(kN,kN)` has `|φ_j| ≥ k` by (B3), and
   `|φ_j| = kN(α_j+β_j) + O(1)`. Hence `α_j + β_j > 0`.
4. **B4.** If `β_j = 0`, then `ℓ_j = δg_j ≥ 0` on colour-2 edges.
   - It sums to 0 around colour-2 cycles, so `φ_j` is empty on `E_2`.
   - (B2) then gives `φ_j(e) = φ_j(e')` on squares, and by (R3) `φ_j` is a constant word
     `w_j` on `E_1`.
   - By B3, `|w_j| = α_j > 0`.
5. **B5.** If such a `j` exists, all colour-1 bricks at a vertex lie in
   `{c_j ∈ w_jC}`, a proper subset of `C^m`. That contradicts (B1). So all `β_j > 0`,
   and symmetrically all `α_j > 0`.
6. **B6.** A primitive `M_1` has cycles whose lengths have gcd 1. Each `α_jp` is an
   integer, so `α_j ∈ Z_{≥1}` by Bézout, and `m ≤ α`.
