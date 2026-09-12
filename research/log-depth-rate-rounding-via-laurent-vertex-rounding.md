---
rg: 2
id: log-depth-rate-rounding-via-laurent-vertex-rounding
kind: route
title: A Laurent-vertex rounding restricts to a polynomial-vertex rounding of depth zero, so the log-depth rate holds trivially
target: vertex-rounding-with-log-depth-rate
requires:
  - laurent-vertex-rounds-for-every-model
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

So input 2 of the non-hyperlinear chain implies input 1. Input 2 is at least as strong, not a parallel alternative.

- Take `ρ_n : Δ -> U(n')` from `laurent-vertex-rounds-for-every-model`, and set `π_n = ρ_n|Γ`.
- Enlarge `F_Δ` to contain `F_Γ`. The closeness bound on `F_Δ` then gives (H1) on `F_Γ`.
- By artifact Lemma 6.1, `ρ_n` factors through a finite ring `L/J` in which every `x_i` is a unit, so every constituent of `π_n` is of unit type.
- So the maximal non-unit root depth is `D(π_n) = 0`, and `δ_n^2 · log(1 + D(π_n)) = 0` for any unitary representatives of `σ_n(A)`.
  - `δ_n <= 2` on the finite set where it is measured, so the product is identically zero.
- This is `vertex-rounding-with-log-depth-rate`.

No converse is known. See `laurent-extension-agrees-iff-inverse-defects-commute` for what a converse needs.
