---
rg: 2
id: sl3z-every-cocompact-quotient-far-from-finite-actions-proof
kind: route
title: Theorem E with superrigidity in place of Bass-Milnor-Serre: defect-free labels give finite holonomy for any cocompact Λ, and norm drift forbids finite orbits
target: sl3z-every-cocompact-quotient-far-from-finite-actions
requires:
  - sl3z-cocompact-microstates-carry-flat-lambda-labels
  - sl3z-maps-to-cocompact-lattices-have-finite-image
---

Only step 2 of `sl3z-cocompact-quotient-uniformly-far-from-finite-actions-proof` changes. Every other step uses
only cocompactness of `Λ`, and so does the flat-labels claim, whose constants `ε_0`, `η`, `B` and `θ_*` come
from a compact fundamental domain.

Take `ε_E < ε_0` with `η(ε_E) < κ/12`, as in `sl3z-cocompact-microstates-carry-flat-lambda-labels`, and suppose
every pair is good at scale `ε_E`.

1. **Holonomy.** By item 3 of that claim, `SL_3(Z)` acts on `Ω = V × Λ`, and the stabilizer of `(v, μ)` is the
   kernel of a homomorphism `ρ_v : Γ_v → Λ` on the finite-index stabilizer `Γ_v`.
2. **Finite image.** By `sl3z-maps-to-cocompact-lattices-have-finite-image`, `ρ_v` has finite image, so
   `ker ρ_v` has finite index in `SL_3(Z)`.
3. **Finite orbits.** Every `SL_3(Z)`-orbit on `Ω` is finite. The union `O` of the orbits through `V × {1}` is
   finite, invariant under every `σ̃_s`, and has no bad pairs.
4. **Drift.** By item 4 of the flat-labels claim, every finite `σ̃`-invariant subset has a proportion at least
   `θ_* > 0` of bad pairs. Contradiction. ∎
