---
rg: 2
id: sfts-without-finite-orbits-not-residually-finite-proof
kind: route
title: A close finite model on the SFT shape assembles into a finite-orbit point of the SFT
target: sfts-without-finite-orbits-are-not-residually-finite-actions
requires: []
artifacts:
  - research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md
---

## Why sufficient

1. **Conventions.** `(lambda . x)(mu) = x(mu lambda)`. `Y` is cut out by allowed patterns on a finite shape `K` containing `e`. By compactness there is `epsilon_0 > 0` such that `d(x, x') < epsilon_0` implies `x(e) = x'(e)`, since the first-coordinate partition has a positive Lebesgue number.
2. **Finite model.** Residual finiteness with `F = K` and `epsilon = epsilon_0` gives a finite `E ⊆ X` with a genuine `Lambda`-action `beta` and `d(s . z, beta(s) z) < epsilon_0` for all `z` in `E` and `s` in `K`. Fix `z_0` in `E`.
3. **Assembly.** Put `y(lambda) = (beta(lambda) z_0)(e)`. For `s` in `K`, apply step 2 to `z = beta(lambda) z_0`:
   `y(s lambda) = (beta(s) beta(lambda) z_0)(e) = (s . beta(lambda) z_0)(e) = (beta(lambda) z_0)(s)`.
   So the `K`-pattern of `y` at `lambda` is the `K`-pattern of `beta(lambda) z_0`, a point of `X ⊆ Y`. It is allowed, and `y ∈ Y`.
4. **Finite orbit.** `L = Stab_beta(z_0)` has finite index. For `l` in `L`, `y(lambda l) = y(lambda)`, so `y` has a finite `Lambda`-orbit. This contradicts the hypothesis on `Y`.
5. **Periodic approximations.** (PA) with this `K` requires a finite-orbit configuration whose `K`-patterns all occur in `X`. Such a configuration lies in `Y`, which has no finite orbit.
6. **The case `Z^2`.** An aperiodic `Z^2` SFT has no finite orbit, by the definition of aperiodic (no nontrivial period). So items 1 and 2 apply to every closed invariant subset of it, and the two cited obstructions have unsatisfiable hypotheses there.
