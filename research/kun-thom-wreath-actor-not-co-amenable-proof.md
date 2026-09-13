---
rg: 2
id: kun-thom-wreath-actor-not-co-amenable-proof
kind: route
title: A translation-invariant mean on the affine lamp space kills zero and becomes a Kazhdan-forbidden mean
target: kun-thom-wreath-actor-subgroups-are-not-co-amenable
requires: [kun-thom-nonsofic-wreath, kun-thom-wreath-sofic-radical-is-fibre-parity-kernel]
artifacts:
  - research/artifacts/kun-thom-wreath-co-amenability-2026-09-12.md
---

Complete proof: Proposition K and Corollaries K1–K3 of the artifact.

1. **The coset space.** `W/(M ⋊ G) ≅ V = B^(X)/M`, with `(n, g)` acting by `v ↦ n + g.v`.
2. **Zero has mass 0.** An invariant mean is translation invariant and `V` is infinite, so `m({0}) = 0`.
3. **Contradiction.** The mean is then `G`-invariant on `V \ {0}`, all of whose orbits are infinite.
   - Day's trick and square roots give almost invariant unit vectors in `ℓ^2(V \ {0})`.
   - Property (T) gives a nonzero invariant vector, which is constant on an orbit.
   - Square-summability forces a finite orbit, a contradiction.
4. **Instances.**
   - **`M = 0`.** A nonzero configuration with a finite orbit has a finite-index stabilizer preserving its
     finite support. That gives finite orbits on `X`, which the hypothesis excludes.
   - **`M = N_0`.** `V ≅ (Z/2)^(G/Γ̂)` through fibre sums, and `G/Γ̂ ≅ SL_d(Z)` is infinite and transitive.
     (T) for the Theorem E group `G` is from `kun-thom-nonsofic-wreath`, and the identification of `N_0` is
     from `kun-thom-wreath-sofic-radical-is-fibre-parity-kernel`.
5. **Actor image.** Pushing a mean forward to `G/π(H)` and applying (T) gives `[G : π(H)] < ∞`.
