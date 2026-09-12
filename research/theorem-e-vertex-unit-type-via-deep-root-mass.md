---
rg: 2
id: theorem-e-vertex-unit-type-via-deep-root-mass
kind: route
title: Round the vertex, bound the non-unit projection by root mass, and kill the shallow and the deep root mass
target: theorem-e-vertex-rounds-to-unit-type-representations
requires:
  - hs-stable-vertex-rounding-for-every-model
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
artifacts:
  - research/artifacts/nh-unit-type-valuations-2026-09-12.md
---

1. **Rounding.** Applying the first premise to the Theorem E pair gives (H1) roundings `π_n`. By item 1 of the second premise,
   each `π_n` factors through `St_r(B_n)` with `B_n = A_u × A_nu` finite.
2. **Projection bound.** `χ|A_nu ≠ 1` iff `depth_nu(χ) >= 1`, so the third premise gives
   `τ(1 − P_n) <= r(r−1)·[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
3. **Both terms vanish.** Item 5 of the fourth premise kills the shallow term, and the fifth premise kills the deep term.
   So `τ(1 − P_n) -> 0` along `U`.
4. **Unit type.**
   - `P_n` is central in `π_n(Γ)''`, so `π_n P_n ⊕ 1_(1−P_n)` is a genuine representation.
   - It factors through `St_r(A_u)`, in which every `x_i` is a unit.
   - It moves each generator by at most `2τ(1 − P_n)^(1/2)` in normalized 2-norm.

The route stays open while its first and fifth premises are open.
