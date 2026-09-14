---
rg: 2
id: invertible-ancilla-outputs-collapse-proof
kind: route
title: Substitute the right inverse into the identity tracks, then set the new ancilla variables to zero
target: invertible-ancilla-outputs-collapse-stable-formalization
requires: []
artifacts:
  - research/artifacts/stable-formalization-erasure-audit-2026-09-12.md
---

Section 2 of the artifact.
1. **Right inverse.** `Φ ∘ Θ = id` forces `Θ_X = X` and `V(X, θ(X, Y')) = Y'` formally.
2. **Substitute.** Put `Y := θ(X, Y')` in `σ~'(U, V) = (X, Y)`. This gives
   `σ~'(U(X, θ(X, Y')), Y') = (X, θ(X, Y'))`.
3. **Set `Y' := 0`.** The `X`-component reads `σ~'_X(U(X, θ(X, 0)), 0) = X` formally.
4. **Points.** `Φ` is the identity on points, so `θ(x, 0) = 0`. Hence `U(x, θ(x, 0)) = τ(x)`.
5. **Left inverse.** `σ'_X(·, 0)` is a left inverse of `τ`, because `σ'(τ(x), 0) = (x, 0)`.

Corollaries 2.2–2.5 follow from this route together with the cited nodes.
