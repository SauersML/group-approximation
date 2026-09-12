---
rg: 2
id: compressor-transport-exactifies-proof
kind: route
title: Average the approximate intertwiner over a finite quotient and take its polar part
target: compressor-transport-exactifies-under-vertex-rounding
requires: []
artifacts:
  - research/artifacts/nh-unit-type-rounding-2026-09-12.md
---

Full derivation in §1 of the artifact.

- **Defect.** `A s A^(-1)` is a fixed word in `F_Γ` and `σ` is a homomorphism into the ultraproduct. So
  `δ_n <= ||σ_n(A)σ_n(s) - σ_n(AsA^(-1))σ_n(A)||_2 + O(max_s ||σ_n(s) - π_n(s)||_2) -> 0`.
- **Averaging.** `π_n` and `ρ_n` factor through finite quotients of `Γ` (root torsion, item 1 of
  `unit-type-vertex-rounding-forces-compressor-commutant-rigidity`). So the projection `E` onto
  invariants of `Φ(γ)X = ρ_n(γ)Xπ_n(γ)^*` is an average of operator-norm contractions.
- **Kazhdan.** Property (T) of `Γ` (Ershov–Jaikin-Zapirain) gives
  `||X - E X||_2 <= κ^(-1) max_s ||Φ(s)X - X||_2`. With `X = U_n` and `T = E(U_n)` this is
  `||U_n - T||_2 <= δ_n/κ`, `||T|| <= 1`, and `T` intertwines.
- **Support bound.** `||1 - T^*T||_2 <= ||U^*(U - T)||_2 + ||(U - T)^* T||_2 <= 2δ_n/κ`. For the
  support `Q` of `T^*T`: `τ(1 - Q) = ||(1 - T^*T)(1 - Q)||_2^2 <= 4δ_n^2/κ^2`.
- **Polar part.** `W = T|T|^(-1)` on `Q` intertwines. Finite dimension gives `τ(1 - Q') = τ(1 - Q)`.
- **Spectral measures.** `ρ_n(e_12(f)) = π_n(e_12(φ_A f))`, so `ρ_n|e_12` has spectral measure `D_A* μ_n`.
  The restrictions to `Q` and `Q'` are unitarily equivalent, so the two measures differ on any set by at
  most `τ(1 - Q)`.
