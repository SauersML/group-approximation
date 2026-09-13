---
rg: 2
id: circle-rotation-zd-codings-are-not-of-finite-type-proof
kind: route
title: A rational perturbation that keeps the cyclic order of the pattern breakpoints gives periodic configurations with legal windows
target: circle-rotation-zd-codings-are-not-of-finite-type
requires: []
artifacts:
  - research/artifacts/zp-fp-simple-amenable-obstructions-2026-09-13-part3.md
---

## Why sufficient

Full proof in the artifact, Section 2.

1. **Freeness.** Suppose `c ∈ X` has period `u ≠ 0`, and put `t = u·θ ∉ Z`.
   - The set where `f(z) ≠ f(z + t)` contains an arc `J` of positive length; otherwise
     `f` would be invariant under the dense group `Zt`, hence constant.
   - A coding agreeing with `c` on a large box has some orbit point in `J`, where the
     period fails.
2. **Patterns.** On `B(r)` the pattern of `z` is constant on the arcs between
   consecutive points of `Σ = {e − k·θ : e ∈ E, k ∈ B(r)}`. So the set of patterns
   depends only on the cyclic order of `Σ` with coincidences.
3. **Perturbation.**
   - Coincidences in `Σ` are exactly `e ∼ e'` (same `Z^d·θ + Z` class) with
     `v_e − v_(e') = k − k'`.
   - Set `e' = e_0 + v_e·θ'` in each class. Every coincidence persists, distinct points
     stay distinct in the same order for `θ'` near `θ`, and rational `θ'` are dense.
4. **Periodic legal configuration.** `y(n) = f'(n·θ')` has a finite orbit, and its
   `B(r)`-windows are patterns of `X`. By step 1, `y ∉ X`.
5. **Not of finite type.** An SFT equals the set of configurations with legal
   `B(r)`-windows for some `r`. Step 4 refutes this for every `r`.
