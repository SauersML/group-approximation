---
rg: 2
id: nonzero-euler-characteristic-blocks-symmetric-sigma-proof
kind: route
title: "Euler characteristic obstruction to symmetric BNSR classes, via Bieri-Renz openness and multiplicativity"
target: nonzero-euler-characteristic-blocks-symmetric-sigma
requires: []
artifacts:
  - research/artifacts/zp-graph-braid-sigma-2026-09-13-part1.md
---

1. Suppose `U = Σ^d(G;ℤ) ∩ −Σ^d(G;ℤ) ≠ ∅`. `U` is open, because
   `Σ^d(G;ℤ)` is open (Bieri–Renz, Comment. Math. Helv. 63 (1988)) and the
   antipodal map is a homeomorphism.
2. Rational character classes are dense in `S(G)`, so `U` contains `[χ]`
   with `χ(G) = ℤ`.
3. By Bieri–Renz, `N = ker χ` is of type `FP_d`. Since
   `cd N ≤ cd G ≤ d`, `N` is of type FP (Brown VIII.6.1).
4. The extension `1 → N → G → ℤ → 1` has FP kernel and quotient, so
   `e(G) = e(N)·e(ℤ) = 0` (Brown IX.7.3). This contradicts `e(G) ≠ 0`.
5. For `m ≥ d`: `Σ^m(G) ⊆ Σ^m(G;ℤ) ⊆ Σ^d(G;ℤ)`.

Full write-up: artifact part 1, §2.
