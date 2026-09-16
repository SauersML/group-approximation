---
rg: 2
id: theorem-e-unit-type-via-instance-vertex-rounding
kind: route
title: Round the Theorem E vertex by the instance claim, bound the non-unit projection by root mass, and kill the shallow and deep root mass
target: theorem-e-vertex-rounds-to-unit-type-representations
requires:
  - theorem-e-vertex-rounds-at-every-actor-model
  - unit-type-vertex-rounding-forces-compressor-commutant-rigidity
  - nonunit-projection-bounded-by-root-spectral-mass
  - shallow-nonunit-root-mass-vanishes-under-vertex-rounding
  - vertex-rounding-deep-nonunit-root-mass-vanishes
artifacts:
  - research/artifacts/nh-unit-type-valuations-2026-09-12.md
---

This is `theorem-e-vertex-unit-type-via-deep-root-mass`, with the rounding premise restated at the Theorem E
pair.
- That route required `hs-stable-vertex-rounding-for-every-model`, which is refuted in general by
  `vertex-rounding-fails-at-symplectic-product-pair`.
- It used that premise only at the Theorem E pair. The instance is `theorem-e-vertex-rounds-at-every-actor-model`.

1. **Rounding.** The first premise gives (H1) roundings `π_n` at the Theorem E pair. By item 1 of the second
   premise, each `π_n` factors through `St_r(B_n)` with `B_n = A_u × A_nu` finite.
2. **Projection bound.** `χ|A_nu ≠ 1` iff `depth_nu(χ) >= 1`. So the third premise gives
   `τ(1 − P_n) <= r(r−1)·[μ_n(depth_nu = 1) + μ_n(depth_nu > 1)]`.
3. **Both terms vanish.** Item 5 of the fourth premise kills the shallow term, and the fifth premise kills the
   deep term. So `τ(1 − P_n) -> 0` along `U`.
4. **Unit type.**
   - `P_n` is central in `π_n(Γ)''`, so `π_n P_n ⊕ 1_(1−P_n)` is a genuine representation.
   - It factors through `St_r(A_u)`, in which every `x_i` is a unit.
   - It moves each generator by at most `2τ(1 − P_n)^(1/2)` in normalized 2-norm.

The route stays open while its first premise is open. Its other four premises are recorded as established.
