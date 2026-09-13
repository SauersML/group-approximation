---
rg: 2
id: extensions-of-aperiodic-sfts-not-rf-proof
kind: route
title: A finite model upstairs transports to distinct nearby points downstairs
target: extensions-of-aperiodic-sfts-are-not-residually-finite-actions
requires:
  - sfts-without-finite-orbits-are-not-residually-finite-actions
  - minimal-aperiodic-wang-shift-exists
artifacts:
  - research/artifacts/labbe-lef-2026-09-12.md
---

## Why sufficient

1. **Scales.** Given finite `F` and `epsilon > 0`, choose `eta <= epsilon/3` with two properties. Both exist by uniform continuity on compact spaces.
   - `d(y, y') < eta` implies `d(pi y, pi y') < epsilon/3`.
   - `d(x, x') < eta` implies `d(s.x, s.x') < epsilon/3` for every `s ∈ F`.
2. **Model upstairs.** Residual finiteness of `Y` gives a finite `eta`-dense `E ⊆ Y` and an action `beta` on `E` with `d(s.e, beta(s) e) < eta` for all `e ∈ E` and `s ∈ F`.
3. **Transport.**
   - `X` has no isolated points, so there are pairwise distinct `x_e ∈ X` with `d(x_e, pi e) < eta`.
   - Put `E' = {x_e : e ∈ E}` and `beta'(s) x_e = x_{beta(s) e}`. This is an action of `Lambda` on `E'`.
4. **Closeness.** For `s ∈ F`, using `s.pi e = pi(s.e)`:

   ```text
   d(s.x_e, x_{beta(s)e}) <= d(s.x_e, s.pi e) + d(pi(s.e), pi(beta(s)e)) + d(pi(beta(s)e), x_{beta(s)e}).
   ```

   Each of the three terms is `< epsilon/3`, so the total is `< epsilon`.
5. **Density.** For `x ∈ X`, pick `y ∈ pi^{-1}(x)` and `e ∈ E` with `d(y, e) < eta`. Then `d(x, x_e) <= d(pi y, pi e) + d(pi e, x_e) < 2 epsilon/3`. This proves item 1.
6. **Item 2.** `Lambda ~ X` is not residually finite, by `sfts-without-finite-orbits-are-not-residually-finite-actions`, item 1. If some extension were residually finite, item 1 would make `X` residually finite.
7. **Item 3.**
   - `Omega_U` is an infinite minimal aperiodic `Z^2`-SFT (`minimal-aperiodic-wang-shift-exists`). So it has no isolated points and no finite orbit, and item 2 applies.
   - If `sigma^v y = y`, then `sigma^v pi y = pi y`, so `v = 0`. Hence `Y` is free.
   - `g -> ĝ` is a homomorphism: `c_{gh}(x) = c_g(h x) + c_h(x)`, and `pi(ĥ y) = h(pi y)`.
   - It is injective: if `ĝ = id`, freeness gives `c_g ∘ pi = 0`, so `c_g = 0` on `pi(Y) = Omega_U`.
   - Theorem C assumes a residually finite action, which item 2 excludes.
