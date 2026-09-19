---
rg: 2
id: thompson-f-fixed-dimension-constants-exceed-four
kind: claim
title: Thompson's F has certified fixed-dimension commutator constants above 4 by dimension 64 (4.45 at 128), and fixed-separation searches below the witness separation only see the best ratio
distinct_from:
  thompson-f-commutator-bound-holds-in-each-fixed-dimension: that proves every C_n(F) finite, reduces nonhyperlinearity to sup_n C_n(F) < infinity, and certifies C_n(F) >= 3.2286 from one four-dimensional pair; this certifies C_16 >= 3.536, C_32 >= 3.98, C_64 >= 4.23 and C_128 >= 4.45, and proves the defect-profile facts that explain why low-floor searches stalled near 3.23.
  thompson-f-in-permanence-closure-only-via-base-copy: that rules out permanence gluings as a route to hyperlinearity of F; here the Baumslag--Gersten group, which is in the permanence closure, is only a numerical calibration.
  baumslag-gersten-mark-survives-opnorm-corona: its route baumslag-gersten-primitive-shell-microstates closes an operator-norm seam with a sorted primitive-shell matcher on 3-power levels; here a prime-orbit spectral matcher gives explicit Hilbert--Schmidt models of BG with exact separation 2 - 2/(m-1), used only to calibrate the defect profile.
artifacts:
  - experiments/thompson-f-defect-profile-2026-09-17/defect_profile.py
  - experiments/thompson-f-defect-profile-2026-09-17/certify_ratio.py
  - experiments/thompson-f-defect-profile-2026-09-17/certify_all.sh
  - experiments/thompson-f-defect-profile-2026-09-17/certify.out
  - experiments/thompson-f-defect-profile-2026-09-17/certify_n128.out
  - experiments/thompson-f-defect-profile-2026-09-17/bg_explicit.py
  - experiments/thompson-f-defect-profile-2026-09-17/bg_explicit.out
  - experiments/thompson-f-defect-profile-2026-09-17/sweep.out
  - experiments/thompson-f-defect-profile-2026-09-17/sweep_tau18.out
  - experiments/thompson-f-defect-profile-2026-09-17/witness_runs.out
  - experiments/thompson-f-defect-profile-2026-09-17/warm_runs.out
  - experiments/thompson-f-defect-profile-2026-09-17/warm_runs64.out
  - experiments/thompson-f-defect-profile-2026-09-17/warm_runs128.out
  - experiments/thompson-f-defect-profile-2026-09-17/warm_runs256.out
---

**Setting.** `F = <a, b | R_1, R_2>` with `R_1 = [ab^-1, a^-1ba]` and `R_2 = [ab^-1, a^-2ba^2]`, and `c = [a,b]`.
For `X` in `U(n)` put `e(X) = ||X - I||_2^2 = 2 - 2 Re tr_n X` (normalized trace). `C_n = C_n(F)` is the least
constant with `e(c) <= C_n^2 max_i e(R_i)` on `U(n)^2`, as in `thompson-f-commutator-bound-holds-in-each-fixed-dimension`
(there, `F` is hyperlinear iff `sup_n C_n = infinity`). The defect profile is

```text
D_n(tau) = inf { max_i e(R_i(U,W)) : U, W in U(n), e(c(U,W)) >= tau },    0 < tau < 4.
```

**Statement.**

1. **Certified constants.** `C_16 >= 3.536`, `C_32 >= 3.98`, `C_64 >= 4.23` and `C_128 >= 4.45`. So `C_n >= 4.45`
   for every `n >= 128`.
   Each bound comes from an explicit pair in `U(n)` with Gaussian-rational Cayley parameters. The inequality
   `e(c) >= B^2 max(e(R_1), e(R_2))` is checked in exact rational arithmetic. The previous record was
   `C_n >= 3.2286` for `n >= 4`.
2. **The profile carries only the ratio.**
   - (a) `D_n(tau) >= tau / C_n^2` for all `n` and `tau`.
   - (b) If a pair in `U(m)` has `e(c) = sigma` and `max e(R_i) = rho`, then `D_(km)(tau) <= rho ceil(k tau/sigma) / k`
     for all `k >= 1` and `tau <= sigma`.
   - (c) So along multiples of `m`, `limsup_k D_(km)(tau) <= tau rho/sigma`. Below the separation of the best pair, a
     search at floor `tau` can do no better than rescale that pair's ratio. It sees no invariant beyond the ratio.
3. **Dichotomy.** Put `D_inf(tau) = liminf_n D_n(tau)`. Then `D_inf(tau) >= tau / (sup_n C_n)^2` for every `tau`.
   The following are equivalent: `D_inf(tau) = 0` for some `tau in (0,2)`; `D_inf(tau) = 0` for all `tau in (0,2)`;
   `F` is hyperlinear.
4. **Calibration family (Baumslag--Gersten).** Let `BG = <a, t | b^-1 a b = a^2, b = t^-1 a t>`, with separating word
   `[a,t]`. (For context only, not used: every finite-dimensional unitary representation of `BG` has `a = I`, because its
   finite quotients are cyclic.) For every prime `m` such that `2` is a primitive root mod `m`, there are `A, T` in
   `U(m)` with
   - `e(B^-1 A B A^-2) <= 8 pi^2 (2m-1) / (3 m^2 (m-1))`, where `B = T^-1 A T`, and
   - `e([A,T]) = 2 - 2/(m-1)`.

   The measured values satisfy `m^2 e(R) -> 6.58`.

Derivation: `thompson-f-fixed-dimension-constants-exceed-four-proof`.

**Evidence, not part of the claim.** All of it is float search, so every number below is an upper bound on `D_n`
only. The scripts, seeds and outputs are in `experiments/thompson-f-defect-profile-2026-09-17/`.

- **Mixing floor at `tau = 1`.** Cold-start Adam searches for `F` plateau at `D_n(1) ~ 0.12` for `n = 4, 8, 16, 32`,
  which is ratio `~ 8.3`. That is below the `n = 4` ratio `10.4`. Item 2 says a floor below a witness's separation
  only rescales its ratio. The 2026-09-16 searches used floors `0.01` to `0.5`, and this is why they stalled near
  `3.23`.
- **The growth came from high separation plus warm-start doubling.** Floor `tau = 1.8`, with dimension-`2m` searches
  seeded by two block copies of the best dimension-`m` pair plus noise, gave these squared ratios `C^2`:

  | `n` | 4 | 16 | 32 | 48 | 64 | 128 |
  |---|---|---|---|---|---|---|
  | `C^2` | 10.40 | 12.51 | 15.91 | 15.97 | 17.94 | 20.16 |

  Up to `n = 128` this is roughly `C_n^2 ~ 2 + 2.6 log_2 n`. Cold starts at `n = 32` managed only `9.5`.
  The `n = 256` rung (800 steps, learning rate `0.01`, `warm_runs256.out`) did not converge. It reached only
  `10.6`, which is below its own noise-free seed, since the block copy already has ratio `20.16`. So the ladder
  stops at `n = 128` because of the optimizer budget. This rung says nothing about `C_256`.
- **Calibration at `tau = 1.8`.** Best upper bounds on `D_n(1.8)` at `n = 4, 8, 16`:
  - `F`: `0.298, 0.210, 0.144`.
  - `BG` (sofic, in the permanence closure): `0.136, 0.015, 0.0033`.
  - Higman's `H_4` (soficity OPEN, `higman-group-is-sofic`): `0.149, 0.053, 0.060`.
- **Witness shape.** The certified pairs keep `c` close to `I` on about a third of the space: the `n = 32` pair has 10
  singular values of `c - I` below `10^-2`. They are not spread over the whole space.
- **Doubling is not a block perturbation.** Write the dimension-`2m` optimum in the basis of its seed
  `I_2 (x) (dimension-m pair)`. The normalized Hilbert--Schmidt mass of the off-diagonal blocks is about `0.25` at
  `n = 32`, and about `0.67` at `n = 64` and `n = 128`. So the gain per doubling comes from real coupling across
  the two copies. A proof of growth would need a doubling map that creates this coupling.

**What this changes.** The numerics had been read as saturating near `3.23`, since the `n = 6` search was worse than
`n = 4`. That was a search artifact, and the certified constants keep growing through `n = 128`. This is not evidence
of unboundedness: a monotone sequence of lower bounds can never prove divergence. But it removes the only numerical
hint of a bounded `sup_n C_n`, which is exactly `thompson-f-is-not-hyperlinear`.
